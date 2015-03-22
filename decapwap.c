/*_
 * Copyright 2010 Scyphus Solutions Co.,Ltd.  All rights reserved.
 *
 * Authors:
 *      Hirochika Asai  <asai@scyphus.co.jp>
 */

/* $Id: decapwap.c,v 0c6c84a5ee88 2011/03/16 06:50:57 Hirochika $ */

#include "config.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <pcap.h>
#include <sys/queue.h>

#define CAPWAP_PORT 5247
#define SWAPZ(a, b) (((a) != (b)) && ((a) ^= (b), (b) = (a) ^ (b), (a) ^= (b)))

/*
 * Fragment entry
 */
struct frag_ent {
    SLIST_ENTRY(frag_ent) entries;
    uint32_t ip4_src;
    uint32_t ip4_dst;
    unsigned int fragid;
    struct pcap_pkthdr pkthdr;
    u_char *pkt;
};

/*
 * Global variables
 */
/* Define the head of fragment entry queue */
SLIST_HEAD(fragq_head, frag_ent)
head = SLIST_HEAD_INITIALIZER(head);
/* Swap control variables */
int swap_frame_control = 1;
int swap_duration = 0;

/*
 * Prototypes of functions
 */
static void usage(const char *);
static uint16_t bytes2uint16(unsigned char *);
static uint32_t bytes2uint32(unsigned char *);
int proc_ipv4(u_char *, const struct pcap_pkthdr *, const u_char *, int);
void cb_dumper(u_char *, const struct pcap_pkthdr *, const u_char *);

/*
 * Print usage
 */
static void
usage(const char *progname)
{
    fprintf(stderr, "Usage: %s capwap-filename output-filename\n", progname);
    exit(EXIT_FAILURE);
}

/*
 * Convert byte stream to uint16_t in the network endian
 */
static uint16_t
bytes2uint16(unsigned char *bytes)
{
    int i;
    uint16_t res;

    res = 0;
    for ( i = 0; i < 2; i++ ) {
        res <<= 8;
        res |= (uint16_t)bytes[i];
    }

    return res;
}

/*
 * Convert byte stream to uint32_t in the network endian
 */
static uint32_t
bytes2uint32(unsigned char *bytes)
{
    int i;
    uint32_t res;

    res = 0;
    for ( i = 0; i < 4; i++ ) {
        res <<= 8;
        res |= (uint32_t)bytes[i];
    }

    return res;
}

/*
 * Process IPv4 packet
 */
int
proc_ipv4(u_char *user, const struct pcap_pkthdr *h, const u_char *bytes,
          int offset)
{
    /* IP addresses */
    uint32_t srcip;
    uint32_t dstip;
    /* Port numbers */
    uint16_t srcport;
    uint16_t dstport;

    /* capwap header */
    unsigned int capwap_hlen;
    unsigned int capwap_rid;
    unsigned int capwap_wbid;
    /* flags of CAPWAP protocol */
    struct {
        unsigned char t:1;
        unsigned char f:1;
        unsigned char l:1;
        unsigned char w:1;
        unsigned char m:1;
        unsigned char k:1;
    } capwap_flags;
    /* Information of fragmentation */
    unsigned int capwap_fragid;
    unsigned int capwap_fragoff;

    /* For storing packets */
    u_char *wrbytes;
    struct pcap_pkthdr nhdr;
    struct frag_ent *ent;

    /* flag */
    int found;

    /* Must be udp; ip>=20byte, udp>=8byte */
    if ( h->caplen < offset+20+8 || 0x11 != bytes[23] ) {
        /* Non udp packet */
        return -1;
    }

    /* Get src IP and dst IP */
    srcip = bytes2uint32((u_char *)bytes+offset+12);
    dstip = bytes2uint32((u_char *)bytes+offset+16);

    /* Skip the IP header */
    offset += 20;

    /* Check udp port */
    srcport = (((uint16_t)bytes[offset])<<8) | ((uint16_t)bytes[offset+1]);
    dstport = (((uint16_t)bytes[offset+2])<<8) | ((uint16_t)bytes[offset+3]);

    /* Skip udp header */
    offset += 8;

    /* check port numbers */
    if ( CAPWAP_PORT != srcport && CAPWAP_PORT != dstport ) {
        /* Not capwap */
        return -1;
    }

    /* Check CAPWAP preamble */
    if ( 0x00 != bytes[offset] ) {
        /* Preamble mismatch */
        return -1;
    }
    /* Check CAPWAP hlen */
    capwap_hlen = ((bytes[offset+1])>>3)&0x1f;
    /* Get rid */
    capwap_rid = (((unsigned int)(bytes[offset+1]&0x7))<<2)
        | (unsigned int)((bytes[offset+2]>>6)&0x3);
    /* Get wbid */
    capwap_wbid = ((unsigned int)(bytes[offset+2]>>1)&0x1f);
    /* Get flags */
    capwap_flags.t = bytes[offset+2]&0x1;
    capwap_flags.f = (bytes[offset+3]>>7)&0x1;
    capwap_flags.l = (bytes[offset+3]>>6)&0x1;
    capwap_flags.w = (bytes[offset+3]>>5)&0x1;
    capwap_flags.m = (bytes[offset+3]>>4)&0x1;
    capwap_flags.k = (bytes[offset+3]>>3)&0x1;
    /* Get fragmentation values */
    capwap_fragid = (((unsigned int)bytes[offset+4]&0xff)<<8)
        | ((unsigned int)bytes[offset+5]&0xff);
    capwap_fragoff = (((unsigned int)bytes[offset+6]&0xff)<<5)
        | ((((unsigned int)bytes[offset+7])>>3)&0x1f);

    /* Skip CAPWAP header */
    offset += 4*capwap_hlen;

    /* Too short packet, then cannot appropriately handle this */
    if ( offset >= h->caplen ) {
        return -1;
    }

    /* Not IEEE802.11 frame, then skip this */
    if ( 1 != capwap_wbid ) {
#if DEBUG
        fprintf(stderr, "non IEEE802.11 frame\n");
#endif
        return -1;
    }
    /* Not native frame, then skip this */
    if ( 1 != capwap_flags.t ) {
#if DEBUG
        fprintf(stderr, "non native frame\n");
#endif
        return -1;
    }

    /* Check the fragmentation flag */
    if ( !capwap_flags.f ) {
        /* If the frame is not fragmented */
        (void)memcpy(&nhdr, h, sizeof(struct pcap_pkthdr));
        nhdr.len = h->len - offset;
        nhdr.caplen = h->caplen - offset;
        wrbytes = (u_char *)bytes + offset;
        /* Swap for wireshark */
        (void)SWAPZ(wrbytes[0], wrbytes[1]);
        /* Store */
        if ( nhdr.caplen > 0 ) {
            pcap_dump(user, &nhdr, wrbytes);
        }
    } else {
        /* If the frame is fragmented, then defragment */
        if ( 0 == capwap_fragoff ) {
            /* Top of fragmented frames */
            ent = malloc(sizeof(struct frag_ent));
            if ( NULL == ent ) {
                fprintf(stderr, "Memory error\n");
                exit(EXIT_FAILURE);
            }
            ent->ip4_src = srcip;
            ent->ip4_dst = dstip;
            ent->fragid = capwap_fragid;
            (void)memcpy(&(ent->pkthdr), h, sizeof(struct pcap_pkthdr));
            ent->pkthdr.len = h->len - offset;
            ent->pkthdr.caplen = h->caplen - offset;
            wrbytes = malloc(sizeof(u_char) * ent->pkthdr.caplen);
            if ( NULL == wrbytes ) {
                fprintf(stderr, "Memory error\n");
                exit(EXIT_FAILURE);
            }
            (void)memcpy(wrbytes, bytes + offset,
                         sizeof(u_char) * ent->pkthdr.caplen);
            /* Swap for wireshark */
            if ( swap_frame_control ) {
                (void)SWAPZ(wrbytes[0], wrbytes[1]);
            }
            if ( swap_duration ) {
                (void)SWAPZ(wrbytes[2], wrbytes[3]);
            }
            ent->pkt = wrbytes;
            /* Insert */
            SLIST_INSERT_HEAD(&head, ent, entries);
        } else {
            found = 0;
            /* Not top, then search identical fragment id */
            SLIST_FOREACH(ent, &head, entries) {
                if ( ent->ip4_src == srcip && ent->ip4_dst == dstip
                     && ent->fragid == capwap_fragid ) {
                    /* Found */
                    found = 1;
                    ent->pkthdr.len += h->len - offset;
                    /* Last fragment? */
                    if ( capwap_flags.l ) {
                        /* Store */
                        if ( ent->pkthdr.caplen > 0 ) {
                            pcap_dump(user, &(ent->pkthdr), ent->pkt);
                        }
                        /* Delete this frag_ent */
                        free(ent->pkt);
                        SLIST_REMOVE(&head, ent, frag_ent, entries);
                        free(ent);
                    }
                    break;
                }
            }
            if ( !found ) {
                fprintf(stderr, "DEFRAGMENTATION ERROR!!!!\n");
            }
        }
    }

    return 0;
}


/*
 * Callback function called from pcap_loop
 */
void
cb_dumper(u_char *user, const struct pcap_pkthdr *h, const u_char *bytes)
{
    /* Offset */
    int offset;
    /* Type in ethernet header */
    uint16_t type;

    /* Proceed to ether type */
    offset = 6 * 2;
    /* Get the frame type */
    type = bytes2uint16((u_char *)bytes+offset);

    /* Check ether type */
    if ( 0x8100 == type ) {
        /* VLAN */
#if DEBUG
        fprintf(stderr, "unsupported protocol: VLAN\n");
#endif
        return;
    } else if ( 0x0806 == type ) {
        /* ARP */
#if DEBUG
        fprintf(stderr, "unsupported protocol: ARP\n");
#endif
        return;
    } else if ( 0x0800 == type ) {
        /* IPv4: supported */
        offset+= 2;
        (void)proc_ipv4(user, h, bytes, offset);
    } else if ( 0x86dd == type ) {
        /* IPv6 */
#if DEBUG
        fprintf(stderr, "unsupported protocol: IPv6\n");
#endif
        return;
    } else if ( type <= 1500 ) {
        /* 802.3: unsupported */
#if DEBUG
        fprintf(stderr, "unsupported protocol: 802.3\n");
        offset+= 2;
#endif
        return;
    } else {
        /* Unsupported */
#if DEBUG
        fprintf(stderr, "unsupported protocol: unknown\n");
#endif
        return;
    }
}

/*
 * main function
 */
int
main(int argc, const char *const argv[], const char *const envp[])
{
    /* Get these from arguments */
    const char *filename = "";
    const char *outfilename = "";
    const char *opt_expr = "";
    /* pcap descriptors */
    pcap_t *pd;
    pcap_t *dpd;
    /* For pcap */
    char errbuf[PCAP_ERRBUF_SIZE];
    struct bpf_program bpfp;
    bpf_u_int32 netmask = 0;
    int optimize = 0;
    /* Definition of the loopback function */
    void cb_dumper(u_char *, const struct pcap_pkthdr *, const u_char *);
    /* dumper */
    pcap_dumper_t *dumper;

    /* Check the arguments */
    if ( argc < 3 ) {
        /* Print a usage sentence and then exit */
        usage(argv[0]);
    }

    /* Get the CAPWAP filename */
    filename = argv[1];
    /* Get the output filename */
    outfilename = argv[2];

    /* Open CAPWAP filename */
    pd = pcap_open_offline(filename, errbuf);
    if ( NULL == pd ) {
        /* error */
        fprintf(stderr, "%s\n", errbuf);
        return EXIT_FAILURE;
    }

    /* Check the linktype */
    if ( DLT_EN10MB != pcap_datalink(pd) ) {
        fprintf(stderr, "Unsupported link type: %d\n", pcap_datalink(pd));
        pcap_close(pd);
        return EXIT_FAILURE;
    }

    /* Compile the filter (not used) */
    if ( pcap_compile(pd, &bpfp, opt_expr, optimize, netmask) < 0 ) {
        /* error */
        pcap_perror(pd, "pcap_compile()");
        pcap_close(pd);
        return EXIT_FAILURE;
    }

    /* Set the compiled filter */
    if ( pcap_setfilter(pd, &bpfp) < 0 ) {
        /* error */
        pcap_perror(pd, "pcap_setfilter()");
        pcap_freecode(&bpfp);
        pcap_close(pd);
        return EXIT_FAILURE;
    }

    /* Initialize the queue. */
    SLIST_INIT(&head);

    /* Open the output file */
    dpd = pcap_open_dead(DLT_IEEE802_11, 0xffff);
    dumper = pcap_dump_open(dpd, outfilename);

    /* Entering the loop, reading packets */
    if ( pcap_loop(pd, 0, cb_dumper, (u_char *)dumper) < 0 ) {
        (void)fprintf(stderr, "%s: pcap_loop: %s\n", argv[0], pcap_geterr(pd));
        pcap_dump_close(dumper);
        pcap_freecode(&bpfp);
        pcap_close(pd);
        return EXIT_FAILURE;
    }

    /* Close dumper and pcap descriptor */
    pcap_dump_close(dumper);
    pcap_freecode(&bpfp);
    pcap_close(pd);

    return EXIT_SUCCESS;
}

/*
 * Local variables:
 * tab-width: 4
 * c-basic-offset: 4
 * End:
 * vim600: sw=4 ts=4 fdm=marker
 * vim<600: sw=4 ts=4
 */
