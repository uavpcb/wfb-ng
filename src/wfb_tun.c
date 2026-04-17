// Copyright (C) 2024 Vasily Evseenko <svpcom@p2ptech.org>

/*
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; version 3.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License along
 *   with this program; if not, write to the Free Software Foundation, Inc.,
 *   51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */


#include <sys/stat.h>
#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <assert.h>
#include <signal.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <event.h>
#include <linux/if.h>
#include <linux/if_tun.h>

// Must be equal to common.radio_mtu !
#define MTU 1445
#define PING_INTERVAL_MS 500

// Mesh relay: dedup cache size (sliding window)
#define RELAY_DEDUP_SIZE 256

// Mesh relay: originator table size and direct-reachability timeout
#define RELAY_ORIG_SIZE 64
#define RELAY_DIRECT_TIMEOUT_MS 3000  // Skip relay if dst seen within this window

#include <time.h>

static uint64_t monotonic_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000ULL + ts.tv_nsec / 1000000ULL;
}

// Mesh relay state
static int relay_enabled = 0;
static uint32_t local_ip_nbo = 0;  // our IP in network byte order
static struct { uint32_t src; uint16_t id; uint8_t in_use; } relay_dedup[RELAY_DEDUP_SIZE];
static int relay_dedup_pos = 0;

// Originator table: when we last heard a packet directly from this src.
// Used to decide whether to relay a packet TO this src's IP.
static struct { uint32_t ip; uint64_t last_heard_ms; uint8_t in_use; } relay_origs[RELAY_ORIG_SIZE];

static uint64_t relay_count_sent = 0;
static uint64_t relay_count_dropped_seen = 0;
static uint64_t relay_count_dropped_direct = 0;

static int relay_seen(uint32_t src, uint16_t ip_id)
{
    for (int i = 0; i < RELAY_DEDUP_SIZE; i++) {
        if (relay_dedup[i].in_use &&
            relay_dedup[i].src == src &&
            relay_dedup[i].id == ip_id)
            return 1;
    }
    relay_dedup[relay_dedup_pos].src = src;
    relay_dedup[relay_dedup_pos].id = ip_id;
    relay_dedup[relay_dedup_pos].in_use = 1;
    relay_dedup_pos = (relay_dedup_pos + 1) % RELAY_DEDUP_SIZE;
    return 0;
}

// Record that we heard a packet from this source. Called on every RX.
static void relay_note_heard(uint32_t ip, uint64_t now_ms)
{
    // Update existing entry
    for (int i = 0; i < RELAY_ORIG_SIZE; i++) {
        if (relay_origs[i].in_use && relay_origs[i].ip == ip) {
            relay_origs[i].last_heard_ms = now_ms;
            return;
        }
    }
    // Add new: find empty or replace oldest
    int oldest_idx = 0;
    uint64_t oldest_t = UINT64_MAX;
    for (int i = 0; i < RELAY_ORIG_SIZE; i++) {
        if (!relay_origs[i].in_use) { oldest_idx = i; break; }
        if (relay_origs[i].last_heard_ms < oldest_t) {
            oldest_t = relay_origs[i].last_heard_ms;
            oldest_idx = i;
        }
    }
    relay_origs[oldest_idx].ip = ip;
    relay_origs[oldest_idx].last_heard_ms = now_ms;
    relay_origs[oldest_idx].in_use = 1;
}

// Is destination dst IP reachable directly (heard recently)?
static int relay_dst_reachable_directly(uint32_t ip, uint64_t now_ms)
{
    for (int i = 0; i < RELAY_ORIG_SIZE; i++) {
        if (relay_origs[i].in_use && relay_origs[i].ip == ip) {
            if (now_ms - relay_origs[i].last_heard_ms < RELAY_DIRECT_TIMEOUT_MS)
                return 1;
        }
    }
    return 0;
}

static struct event_base *ev_base;
static struct event *ev_ping;
static struct event *ev_tun_read;
static struct event *ev_tun_read_timeout;
static struct event *ev_tun_write;
static struct event *ev_socket_write;
static struct event *ev_socket_read;

struct sockaddr_in peer_addr;

static int pkt_sem = 0;
static unsigned int agg_timeout_ms = 5;

typedef struct
{
    char data[MTU * 2];
    size_t data_size;  // size of packet buffer
    size_t batch_size; // size of current ready-to-send batch <= MTU
} in_packet_buffer_t;

typedef struct
{
    char data[MTU];
    size_t data_size;  // size of packet buffer
    size_t offset; // offset of current packet for injection into tun
} out_packet_buffer_t;

// TUN packet header
typedef struct {
    uint16_t packet_size;
}  __attribute__ ((packed)) tun_packet_hdr_t;


// Don't use possible C++ loggers
#ifdef WFB_DBG
#undef WFB_DBG
#endif

#ifdef __DEBUG__
#define WFB_DBG(...)  fprintf(stderr, __VA_ARGS__)
#else
#define WFB_DBG(...)  ((void)0)
#endif


void event_sig_cb(evutil_socket_t sig, short flags, void *arg)
{
    switch (sig)
    {
    case SIGINT:
    case SIGTERM:
        break;

    default:
        assert(0);
    }

    WFB_DBG("Exiting...\n");
    event_base_loopexit (ev_base, NULL);
}

void ev_ping_cb(evutil_socket_t fd, short flags, void *arg)
{
    assert(fd >= 0);
    assert((EV_TIMEOUT & flags) != 0);

    if(pkt_sem == 0)
    {
        WFB_DBG("send ping\n");
        sendto(fd, "", 0, MSG_DONTWAIT, (struct sockaddr*)&peer_addr, sizeof(peer_addr));
    }

    if(pkt_sem > 0) pkt_sem--;
}

void ev_tun_read_cb(evutil_socket_t fd, short flags, void *arg)
{
    in_packet_buffer_t *buf = arg;

    assert(buf != NULL);
    assert((EV_TIMEOUT & flags) == 0);
    assert((EV_READ & flags) != 0);
    assert(ev_tun_read != NULL);
    assert(ev_socket_write != NULL);
    assert(buf->data_size < MTU);

    bool is_new_buffer = (buf->data_size == 0);
    int nread = read(fd,
                     buf->data + buf->data_size + sizeof(tun_packet_hdr_t),
                     MTU - sizeof(tun_packet_hdr_t));

    assert(nread > 0);
    assert(nread <= MTU - sizeof(tun_packet_hdr_t));

    ((tun_packet_hdr_t*)(buf->data + buf->data_size))->packet_size = htons(nread);

    buf->data_size += (sizeof(tun_packet_hdr_t) + nread);

    if (buf->data_size <= MTU)
    {
        buf->batch_size = buf->data_size;
    }

    WFB_DBG("tun_read: packet_size=%d, batch_size=%zu, data_size=%zu\n", nread, buf->batch_size, buf->data_size);

    if(buf->data_size >= MTU || agg_timeout_ms == 0)
    {
        // flush buffer
        event_add(ev_socket_write, NULL);
    }
    else
    {
        // continue aggregation
        event_add(ev_tun_read, NULL);

        if(is_new_buffer && agg_timeout_ms > 0)
        {
            // Set aggregation timeout for new buffer
            struct timeval tv = { .tv_sec = agg_timeout_ms / 1000,
                                  .tv_usec = (agg_timeout_ms % 1000) * 1000 };
            event_add(ev_tun_read_timeout, &tv);
        }

    }
}

void ev_socket_write_cb(evutil_socket_t fd, short flags, void *arg)
{
    in_packet_buffer_t *buf = arg;

    assert(buf != NULL);
    assert(ev_tun_read != NULL);
    assert(ev_socket_write != NULL);

    // reset ping semaphore
    pkt_sem = 1;

    if(flags & EV_WRITE && agg_timeout_ms > 0)
    {
        // reset aggregation timer;
        event_del(ev_tun_read_timeout);
    }

    if(flags & EV_TIMEOUT)
    {
        assert((flags & EV_WRITE) == 0);
        event_del(ev_tun_read);
    }

    assert(buf->batch_size <= MTU);
    sendto(fd, buf->data, buf->batch_size, MSG_DONTWAIT, (struct sockaddr*)&peer_addr, sizeof(peer_addr));

    WFB_DBG("socket_write: batch_size=%zu, data_size=%zu\n", buf->batch_size, buf->data_size);

    if(buf->data_size > buf->batch_size)
    {
        memmove(buf->data, buf->data + buf->batch_size, buf->data_size - buf->batch_size);
        buf->data_size -= buf->batch_size;
        buf->batch_size = buf->data_size;
    }
    else
    {
        memset(buf, 0, sizeof(in_packet_buffer_t));
    }

    assert(buf->data_size <= MTU);

    if(buf->data_size == MTU || (buf->data_size > 0 && agg_timeout_ms == 0))
    {
        event_add(ev_socket_write, NULL);
    }
    else
    {
        event_add(ev_tun_read, NULL);

        if(buf->data_size > 0 && agg_timeout_ms > 0)
        {
            // Set aggregation timeout for non-empty buffer
            struct timeval tv = { .tv_sec = agg_timeout_ms / 1000,
                                  .tv_usec = (agg_timeout_ms % 1000) * 1000 };

            event_add(ev_tun_read_timeout, &tv);
        }
    }
}


void ev_tun_write_cb(evutil_socket_t fd, short flags, void *arg)
{
    out_packet_buffer_t *buf = arg;
    int nwrote;

    assert(buf != NULL);
    assert((EV_TIMEOUT & flags) == 0);
    assert((EV_WRITE & flags) != 0);
    assert(ev_tun_write != NULL);
    assert(ev_socket_read != NULL);

    assert(buf->offset + sizeof(tun_packet_hdr_t) <= buf->data_size);
    uint16_t packet_size = ntohs(((tun_packet_hdr_t*)(buf->data + buf->offset))->packet_size);

    WFB_DBG("tun_write: off=%zu, psize=%zu + %d, data_size=%zu\n", buf->offset, sizeof(tun_packet_hdr_t), packet_size, buf->data_size);
    assert(buf->offset + sizeof(tun_packet_hdr_t) + packet_size <= buf->data_size);

    nwrote = write(fd, buf->data + buf->offset + sizeof(tun_packet_hdr_t), packet_size);
    assert(nwrote == packet_size);

    buf->offset += (sizeof(tun_packet_hdr_t) + packet_size);

    if (buf->offset < buf->data_size)
    {
        event_add(ev_tun_write, NULL);
    }
    else
    {
        memset(buf, 0, sizeof(out_packet_buffer_t));
        event_add(ev_socket_read, NULL);
    }
}


void ev_socket_read_cb(evutil_socket_t fd, short flags, void *arg)
{
    out_packet_buffer_t *buf = arg;
    int nread;

    assert(buf != NULL);
    assert((EV_TIMEOUT & flags) == 0);
    assert((EV_READ & flags) != 0);
    assert(ev_socket_read != NULL);
    assert(ev_tun_write != NULL);

    nread = recv(fd,
                 buf->data,
                 MTU,
                 MSG_DONTWAIT);

    assert(nread >= 0);
    assert(nread <= MTU);

    if(nread == 0)
    {
        // skip ping packet
        event_add (ev_socket_read, NULL);
        WFB_DBG("got ping\n");
        return;
    }

    // Mesh relay: inspect each packet in the batch.
    // Reinject packets that are not for us, haven't been seen before,
    // and have TTL > 1. Sends them back via socket to wfb_tx.
    if (relay_enabled)
    {
        char relay_out[MTU];
        size_t relay_out_size = 0;
        size_t off = 0;
        uint64_t now_ms = monotonic_ms();

        while (off + sizeof(tun_packet_hdr_t) <= (size_t)nread)
        {
            uint16_t psize = ntohs(((tun_packet_hdr_t*)(buf->data + off))->packet_size);
            if (off + sizeof(tun_packet_hdr_t) + psize > (size_t)nread)
                break;

            uint8_t *pkt = (uint8_t*)(buf->data + off + sizeof(tun_packet_hdr_t));

            // Only handle IPv4
            if (psize >= 20 && (pkt[0] >> 4) == 4)
            {
                uint32_t src, dst;
                memcpy(&src, pkt + 12, 4);
                memcpy(&dst, pkt + 16, 4);
                uint16_t ip_id = ntohs(*(uint16_t*)(pkt + 4));
                uint8_t ttl = pkt[8];

                // Note: we heard this src (for future relay decisions)
                if (src != local_ip_nbo)
                    relay_note_heard(src, now_ms);

                // Relay rules:
                //  - source is not me (skip own echo)
                //  - destination is not me (I keep it, not relay)
                //  - TTL > 1 (at least one hop left)
                //  - haven't seen (src, ip_id) before
                //  - destination not reachable directly by us (don't relay if dst is known direct)
                if (src != local_ip_nbo && dst != local_ip_nbo &&
                    ttl > 1 && !relay_seen(src, ip_id) &&
                    !relay_dst_reachable_directly(dst, now_ms))
                {
                    if (relay_out_size + sizeof(tun_packet_hdr_t) + psize <= MTU)
                    {
                        tun_packet_hdr_t *h = (tun_packet_hdr_t*)(relay_out + relay_out_size);
                        h->packet_size = htons(psize);
                        uint8_t *dp = (uint8_t*)(relay_out + relay_out_size + sizeof(tun_packet_hdr_t));
                        memcpy(dp, pkt, psize);

                        // Decrement TTL and recompute IP header checksum
                        dp[8]--;
                        uint8_t ihl = (dp[0] & 0x0f) * 4;
                        if (ihl <= psize) {
                            uint16_t *csum = (uint16_t*)(dp + 10);
                            *csum = 0;
                            uint32_t s = 0;
                            for (int i = 0; i + 1 < ihl; i += 2)
                                s += ntohs(*(uint16_t*)(dp + i));
                            while (s >> 16) s = (s & 0xffff) + (s >> 16);
                            *csum = htons(~s & 0xffff);
                        }

                        relay_out_size += sizeof(tun_packet_hdr_t) + psize;
                        relay_count_sent++;
                    }
                }
                else if (src != local_ip_nbo && dst != local_ip_nbo && ttl > 1)
                {
                    // Either seen already or dst reachable directly
                    if (relay_dst_reachable_directly(dst, now_ms))
                        relay_count_dropped_direct++;
                    else
                        relay_count_dropped_seen++;
                }
            }

            off += sizeof(tun_packet_hdr_t) + psize;
        }

        if (relay_out_size > 0)
        {
            ssize_t sent = sendto(fd, relay_out, relay_out_size, 0,
                                  (struct sockaddr*)&peer_addr, sizeof(peer_addr));
            (void)sent;
        }
    }

    buf->offset = 0;
    buf->data_size = nread;

    WFB_DBG("socket_read: off=%zu, data_size=%zu\n", buf->offset, buf->data_size);

    event_add(ev_tun_write, NULL);
}

static int open_tun(char *dev, char *dev_addr)
{
    struct ifreq ifr;
    int fd, err;

    if((fd = open("/dev/net/tun", O_RDWR | O_NONBLOCK | O_CLOEXEC)) < 0)
    {
        perror("open");
        return -1;
    }

    memset(&ifr, 0, sizeof(ifr));

    /* Flags: IFF_TUN   - TUN device (no Ethernet headers)
     *        IFF_TAP   - TAP device
     *
     *        IFF_NO_PI - Do not provide packet information
     */

    ifr.ifr_flags = IFF_TUN | IFF_NO_PI;

    if(dev != NULL)
    {
        strncpy(ifr.ifr_name, dev, IFNAMSIZ);
    }

    if((err = ioctl(fd, TUNSETIFF, (void *) &ifr)) < 0)
    {
        perror("ioctl");
        close(fd);
        return err;
    }

    if(dev_addr != NULL)
    {
        char buf[256];
        snprintf(buf, sizeof(buf), "ip link set up mtu %zu dev %s", MTU - sizeof(tun_packet_hdr_t), ifr.ifr_name);
        if(system(buf) != 0)
        {
            close(fd);
            return -1;
        }
        snprintf(buf, sizeof(buf), "ip addr add %s dev %s", dev_addr, ifr.ifr_name);
        if(system(buf) != 0)
        {
            close(fd);
            return -1;
        }
    }

    return fd;
}


static int create_udpsock(uint16_t bind_port)
{
    int fd;
    struct sockaddr_in saddr;

    if((fd = socket(AF_INET, SOCK_DGRAM | SOCK_NONBLOCK | SOCK_CLOEXEC, IPPROTO_UDP)) < 0)
    {
        perror("socket");
        return -1;
    }

    const int optval = 1;
    if(setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, (const void *)&optval , sizeof(optval)) !=0)
    {
        perror("setsockopt");
        close(fd);
        return -1;
    }

    memset(&saddr, 0, sizeof(saddr));
    saddr.sin_family = AF_INET;
    saddr.sin_addr.s_addr = htonl(INADDR_ANY);
    saddr.sin_port = htons((unsigned short)bind_port);

    if(bind(fd, (const struct sockaddr *) &saddr, sizeof (saddr)) < 0)
    {
        perror("bind");
        close(fd);
        return -1;
    }

    return fd;
}


int main (int argc, char *argv[])
{
    struct event_config *ev_cfg = NULL;
    struct event *ev_sigint = NULL;
    struct event *ev_sigterm = NULL;

    struct timeval ping_tv = { .tv_sec = PING_INTERVAL_MS / 1000,
                               .tv_usec = (PING_INTERVAL_MS % 1000) * 1000 };

    int tun_fd = -1;
    int sock_fd = -1;

    // buffer TUN -> socket
    in_packet_buffer_t in_buf;

    // buffer socket -> TUN
    out_packet_buffer_t out_buf;

    uint16_t bind_port = 5800;
    char *tun_name = "wfb-tun";
    char *tun_addr = "10.5.0.2/24";
    int opt;

    memset(&in_buf, 0, sizeof(in_buf));
    memset(&out_buf, 0, sizeof(out_buf));

    memset(&peer_addr, 0, sizeof(peer_addr));
    peer_addr.sin_family = AF_INET;
    peer_addr.sin_addr.s_addr = htonl(0x7f000001); // 127.0.0.1
    peer_addr.sin_port = htons(5801);

    while ((opt = getopt(argc, argv, "t:c:u:l:a:T:Rh")) != -1)
    {
        switch (opt)
        {
        case 't':
            tun_name = strdup(optarg);
            break;

        case 'a':
            tun_addr = strdup(optarg);
            break;

        case 'T':
            agg_timeout_ms = atoi(optarg);
            break;

        case 'c':
            if(inet_pton(AF_INET, optarg, &peer_addr.sin_addr) != 1)
            {
                perror("invalid address");
                return 1;
            }
            break;

        case 'u':
            peer_addr.sin_port = htons(atoi(optarg));
            break;

        case 'l':
            bind_port = atoi(optarg);
            break;

        case 'R':
            relay_enabled = 1;
            break;

        default: /* '?' */
            fprintf(stderr, "Usage: %s [-t tun_name] [-a tun_addr] [-c peer_addr] [-u peer_port] [-l listen_port] [-T agg_timeout_ms] [-R]\n", argv[0]);
            fprintf(stderr, "Default: tun_name=%s, tun_addr=%s, peer_addr=127.0.0.1, peer_port=5801, listen_port=%d, agg_timeout_ms=%u\n", tun_name, tun_addr, bind_port, agg_timeout_ms);
            fprintf(stderr, "  -R  Enable mesh relay (reinject packets not destined to our IP, TTL-limited, dedup)\n");
            fprintf(stderr, "WFB-ng version %s\n", WFB_VERSION);
            fprintf(stderr, "WFB-ng home page: <http://wfb-ng.org>\n");
            return 1;
        }
    }

    // Parse local IP from tun_addr (strip /prefix) for relay dedup
    if (relay_enabled && tun_addr != NULL)
    {
        char ip_str[64];
        strncpy(ip_str, tun_addr, sizeof(ip_str) - 1);
        ip_str[sizeof(ip_str) - 1] = 0;
        char *slash = strchr(ip_str, '/');
        if (slash) *slash = 0;
        struct in_addr a;
        if (inet_pton(AF_INET, ip_str, &a) == 1) {
            local_ip_nbo = a.s_addr;
            fprintf(stderr, "wfb_tun: relay enabled, local IP = %s (0x%08x)\n",
                    ip_str, ntohl(local_ip_nbo));
        } else {
            fprintf(stderr, "wfb_tun: could not parse tun_addr '%s' for relay\n", tun_addr);
            return 1;
        }
    }

    // initialize libevent

#ifdef __DEBUG__
    event_enable_debug_mode();
#endif

    ev_cfg = event_config_new();
    assert(ev_cfg != NULL);

    event_config_require_features(ev_cfg, EV_FEATURE_FDS);
    event_config_set_flag(ev_cfg, EVENT_BASE_FLAG_PRECISE_TIMER);

    ev_base = event_base_new_with_config(ev_cfg);
    assert(ev_base != NULL);

    // event for catching interrupt signal
    ev_sigint = evsignal_new(ev_base, SIGINT, &event_sig_cb, NULL);
    evsignal_add(ev_sigint, NULL);

    ev_sigterm = evsignal_new(ev_base, SIGTERM, &event_sig_cb, NULL);
    evsignal_add(ev_sigterm, NULL);

    sock_fd = create_udpsock(bind_port);
    assert(sock_fd >= 0);

    tun_fd = open_tun(tun_name, tun_addr);
    assert(tun_fd >= 0);

    ev_ping = event_new(ev_base, sock_fd, EV_PERSIST, &ev_ping_cb, NULL);
    event_add(ev_ping, &ping_tv);

    ev_tun_read = event_new(ev_base,
                            tun_fd,
                            EV_READ,
                            &ev_tun_read_cb, &in_buf);

    ev_tun_read_timeout = event_new(ev_base,
                                    sock_fd,
                                    EV_TIMEOUT,
                                    &ev_socket_write_cb, &in_buf);

    ev_socket_read = event_new(ev_base,
                               sock_fd,
                               EV_READ,
                               &ev_socket_read_cb, &out_buf);

    ev_tun_write = event_new(ev_base,
                             tun_fd,
                             EV_WRITE,
                             &ev_tun_write_cb, &out_buf);

    ev_socket_write = event_new(ev_base,
                                sock_fd,
                                EV_WRITE,
                                &ev_socket_write_cb, &in_buf);

    assert(ev_tun_read != NULL);
    assert(ev_socket_read != NULL);

    event_add(ev_tun_read, NULL);
    event_add(ev_socket_read, NULL);
    event_base_dispatch(ev_base);

    close(sock_fd);
    close(tun_fd);

    if(ev_sigint) event_free(ev_sigint);
    if(ev_sigterm) event_free(ev_sigterm);
    if(ev_tun_read) event_free(ev_tun_read);
    if(ev_tun_read_timeout) event_free(ev_tun_read_timeout);
    if(ev_tun_write) event_free(ev_tun_write);
    if(ev_socket_read) event_free(ev_socket_read);
    if(ev_socket_write) event_free(ev_socket_write);
    if(ev_ping) event_free(ev_ping);

    event_base_free (ev_base);
    event_config_free (ev_cfg);
    libevent_global_shutdown();

    return 0;
}
