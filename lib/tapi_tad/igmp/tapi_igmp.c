/* SPDX-License-Identifier: Apache-2.0 */
/** @file
 * @brief Test API for TAD IGMP CSAP
 *
 * Implementation of Test API
 *
 * Copyright (C) 2004-2022 OKTET Labs Ltd. All rights reserved.
 */

#define TE_LGR_USER "TAPI IGMPv2"

#include "te_config.h"

#include "te_errno.h"
#include "logger_api.h"
#include "asn_usr.h"
#include "tapi_ndn.h"
#include "ndn_ipstack.h"
#include "ndn_igmp.h"
#include "tapi_igmp.h"

#include "tapi_test.h"


/* See the description in tapi_igmp.h */
te_errno
tapi_igmp_add_csap_layer(asn_value **csap_spec)
{
    asn_value  *layer = NULL;

    return tapi_tad_csap_add_layer(csap_spec, ndn_igmp_csap,
                                   "#igmp", &layer);
}


/* See the description in tapi_igmp.h */
te_errno
tapi_igmp_ip4_eth_csap_create(const char    *ta_name,
                              int            sid,
                              const char    *ifname,
                              unsigned int   receive_mode,
                              const uint8_t *eth_src,
                              in_addr_t      src_addr,
                              csap_handle_t *igmp_csap)
{
    bool ppp_if;
    te_errno    rc;
    asn_value  *csap_spec = NULL;

    ppp_if = (strncmp(ifname, "ppp", strlen("ppp")) == 0);

    do {
        if ((rc = tapi_igmp_add_csap_layer(&csap_spec)) != 0)
        {
            WARN("%s(): add IGMPv2 csap layer failed %r", __FUNCTION__, rc);
            break;
        }

        if ((rc = tapi_ip4_add_csap_layer(&csap_spec,
                                          src_addr,
                                          htonl(INADDR_ANY),
                                          IPPROTO_IGMP,
                                          -1 /* default ttl */,
                                          -1 /* default tos */)) != 0)
        {
            WARN("%s(): add IP4 csap layer failed %r", __FUNCTION__, rc);
            break;
        }

        if (ppp_if)
        {
            rc = asn_write_string(csap_spec, ifname,
                          "layers.1.#ip4.ifname.#plain");
            if (rc != 0)
            {
                asn_free_value(csap_spec);
                WARN("%s(): write IP4 layer value 'ifname' failed %r",
                     __FUNCTION__, rc);
                return rc;
            }

            rc = tapi_tad_csap_create(ta_name, sid, "igmp.ip4",
                                      csap_spec, igmp_csap);
            break;
        }

        if ((rc = tapi_eth_add_csap_layer(&csap_spec, ifname,
                                          receive_mode,
                                          NULL,
                                          eth_src,
                                          NULL, TE_BOOL3_ANY,
                                          TE_BOOL3_ANY)) != 0)
        {
            WARN("%s(): add ETH csap layer failed %r", __FUNCTION__, rc);
            break;
        }

        rc = tapi_tad_csap_create(ta_name, sid, "igmp.ip4.eth",
                                  csap_spec, igmp_csap);
    } while (0);

    asn_free_value(csap_spec);

    return TE_RC(TE_TAPI, rc);
}


/* See the description in tapi_igmp.h */
te_errno
tapi_igmp2_add_pdu(asn_value          **tmpl_or_ptrn,
                   asn_value          **pdu,
                   bool is_pattern,
                   tapi_igmp_msg_type   type,
                   int                  max_resp_time,
                   in_addr_t            group_addr)
{
    asn_value  *tmp_pdu;

    if (type > 0xff || max_resp_time > 0xff)
        return TE_RC(TE_TAPI, TE_EINVAL);

    CHECK_RC(tapi_tad_tmpl_ptrn_add_layer(tmpl_or_ptrn, is_pattern,
                                          ndn_igmp_message, "#igmp",
                                          &tmp_pdu));

    if (type > 0)
        CHECK_RC(asn_write_int32(tmp_pdu, type, "type.#plain"));
    if (max_resp_time >= 0)
        CHECK_RC(asn_write_int32(tmp_pdu, max_resp_time,
                                 "max-resp-time.#plain"));

    INFO("Fill Group Address: 0x%08x", (uint32_t)group_addr);
    if (group_addr != htonl(INADDR_ANY))
        CHECK_RC(asn_write_value_field(tmp_pdu,
                                       &group_addr, sizeof(group_addr),
                                       "group-address.#plain"));

    if (pdu != NULL)
        *pdu = tmp_pdu;

    return 0;
}

/* See the description in tapi_igmp.h */
void
tapi_ip4_to_mcast_mac(in_addr_t ip4_addr, uint8_t *eth_addr)
{
    uint8_t *ip_addr_p = (uint8_t *)&ip4_addr;

    /* Map IP address into MAC one */
    eth_addr[0] = 0x01;
    eth_addr[1] = 0x00;
    eth_addr[2] = 0x5e;
    eth_addr[3] = ip_addr_p[1] & 0x7f;
    eth_addr[4] = ip_addr_p[2];
    eth_addr[5] = ip_addr_p[3];
}

/** Router Alert Option is mandatory */
static uint8_t ip_opt_router_alert[] = {0x94, 0x04, 0x00, 0x00};

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp_add_ip4_pdu_gen(asn_value **tmpl_or_ptrn,
                        asn_value **pdu,
                        bool is_pattern,
                        in_addr_t   dst_addr,
                        in_addr_t   src_addr,
                        int         ttl,
                        int         tos)
{
    te_errno       rc     = 0;
    asn_value     *ip4_pdu;
    int            dont_frag = 1;

    UNUSED(pdu);

    if (dst_addr == htonl(INADDR_ANY))
        dst_addr = TAPI_MCAST_ADDR_ALL_HOSTS;

    if ((src_addr == htonl(INADDR_ANY)) && (!is_pattern))
    {
        WARN("Invalid zero IPv4 source address field is used");
    }

    /* Add IPv4 layer header to PDU template/pattern */
    rc = tapi_ip4_add_pdu(tmpl_or_ptrn, &ip4_pdu, is_pattern,
                          src_addr, dst_addr,
                          IPPROTO_IGMP, ttl, tos);
    if (rc != 0)
        return rc;

    rc = asn_write_int32(ip4_pdu, dont_frag, "dont-frag.#plain");
    if (rc != 0)
        return rc;

    /* Add mandatory Router Alert IP option */
    rc = asn_write_value_field(ip4_pdu,
                             ip_opt_router_alert,
                             sizeof(ip_opt_router_alert),
                             "options.#plain");
    if (rc != 0)
        return rc;

    return rc;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp_add_ip4_pdu(asn_value **tmpl_or_ptrn,
                      asn_value **pdu,
                      bool is_pattern,
                      in_addr_t   dst_addr,
                      in_addr_t   src_addr)
{
    return tapi_igmp_add_ip4_pdu_gen(tmpl_or_ptrn,
                    pdu, is_pattern, dst_addr, src_addr,
                    TAPI_IGMP_IP4_TTL_DEFAULT,
                    TAPI_IGMP_IP4_TOS_DEFAULT);
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp_add_ip4_eth_pdu_gen(asn_value **tmpl_or_ptrn,
                          asn_value **pdu,
                          bool is_pattern,
                          in_addr_t   dst_addr,
                          in_addr_t   src_addr,
                          uint8_t    *eth_src,
                          int           ttl,
                          int           tos)
{
    te_errno       rc     = 0;
    const uint16_t ip_eth = ETHERTYPE_IP;
    uint8_t        eth_dst[ETHER_ADDR_LEN];
    asn_value     *ip4_pdu = NULL;
    asn_value     *eth_pdu = NULL;
    int            dont_frag = 1;

    UNUSED(pdu);

    if (dst_addr == htonl(INADDR_ANY))
        dst_addr = TAPI_MCAST_ADDR_ALL_HOSTS;

    if ((src_addr == htonl(INADDR_ANY)) && (!is_pattern))
    {
        WARN("Invalid zero IPv4 source address field is used");
    }

    /* Add IPv4 layer header to PDU template/pattern */
    rc = tapi_ip4_add_pdu(tmpl_or_ptrn, &ip4_pdu, is_pattern,
                          src_addr, dst_addr,
                          IPPROTO_IGMP, ttl, tos);
    if (rc != 0)
        return rc;

    rc = asn_write_int32(ip4_pdu, dont_frag, "dont-frag.#plain");
    if (rc != 0)
        return rc;

    /* Add mandatory Router Alert IP option */
    rc = asn_write_value_field(ip4_pdu,
                             ip_opt_router_alert,
                             sizeof(ip_opt_router_alert),
                             "options.#plain");
    if (rc != 0)
        return rc;

    /* Calculate MAC multicast address also */
    if (dst_addr != htonl(INADDR_ANY))
        tapi_ip4_to_mcast_mac(dst_addr, eth_dst);

    /* Add Ethernet layer header to PDU template/pattern */
    rc = tapi_eth_add_pdu(tmpl_or_ptrn, &eth_pdu, is_pattern,
                          (dst_addr == htonl(INADDR_ANY)) ? NULL : eth_dst,
                          eth_src,
                          &ip_eth,
                          TE_BOOL3_ANY,
                          TE_BOOL3_ANY);
    if (rc != 0)
        return rc;

    /* Force untagged frames */
    rc = asn_write_value_field(eth_pdu, NULL, 0,
                               "tagged.#untagged");
    if (rc != 0)
        return rc;

    return rc;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp_add_ip4_eth_pdu(asn_value **tmpl_or_ptrn,
                          asn_value **pdu,
                          bool is_pattern,
                          in_addr_t   dst_addr,
                          in_addr_t   src_addr,
                          uint8_t    *eth_src)
{
    return tapi_igmp_add_ip4_eth_pdu_gen(tmpl_or_ptrn, pdu, is_pattern,
                          dst_addr, src_addr, eth_src,
                          TAPI_IGMP_IP4_TTL_DEFAULT,
                          TAPI_IGMP_IP4_TOS_DEFAULT);
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp1_ip4_eth_send_report(const char    *ta_name,
                               int            session,
                               csap_handle_t  csap,
                               in_addr_t      group_addr,
                               in_addr_t      src_addr,
                               uint8_t       *eth_src)
{
    te_errno   rc       = 0;
    asn_value *pkt_tmpl = NULL;

    /* Add IGMPv2 layer message to PDU template/pattern */
    rc = tapi_igmp2_add_pdu(&pkt_tmpl, NULL, false,
                            TAPI_IGMP1_TYPE_REPORT, 0, group_addr);
    if (rc != 0)
        return rc;

    /* Add IPv4 layer header to PDU template/pattern */
    rc = tapi_igmp_add_ip4_eth_pdu(&pkt_tmpl, NULL, false,
                                   group_addr, src_addr, eth_src);
    if (rc != 0)
        return rc;

    rc = tapi_tad_trsend_start(ta_name, session, csap,
                               pkt_tmpl, RCF_MODE_BLOCKING);

    asn_free_value(pkt_tmpl);

    return rc;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp2_ip4_eth_send_report(const char    *ta_name,
                               int            session,
                               csap_handle_t  csap,
                               in_addr_t      group_addr,
                               in_addr_t      src_addr,
                               uint8_t       *eth_src)
{
    te_errno   rc       = 0;
    asn_value *pkt_tmpl = NULL;

    /* Add IGMPv2 layer message to PDU template/pattern */
    rc = tapi_igmp2_add_pdu(&pkt_tmpl, NULL, false,
                            TAPI_IGMP2_TYPE_REPORT, 0, group_addr);
    if (rc != 0)
        return rc;

    /* Add IPv4 layer header to PDU template/pattern */
    rc = tapi_igmp_add_ip4_eth_pdu(&pkt_tmpl, NULL, false,
                                   group_addr, src_addr, eth_src);
    if (rc != 0)
        return rc;

    rc = tapi_tad_trsend_start(ta_name, session, csap,
                               pkt_tmpl, RCF_MODE_BLOCKING);

    asn_free_value(pkt_tmpl);

    return rc;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp2_ip4_eth_send_leave(const char    *ta_name,
                              int            session,
                              csap_handle_t  csap,
                              in_addr_t      group_addr,
                              in_addr_t      src_addr,
                              uint8_t       *eth_src)
{
    te_errno   rc       = 0;
    asn_value *pkt_tmpl = NULL;

    /* Add IGMPv2 layer message to PDU template/pattern */
    rc = tapi_igmp2_add_pdu(&pkt_tmpl, NULL, false,
                            TAPI_IGMP2_TYPE_LEAVE, 0, group_addr);
    if (rc != 0)
        return rc;

    /* Add IPv4 layer header to PDU template/pattern */
    rc = tapi_igmp_add_ip4_eth_pdu(&pkt_tmpl, NULL, false,
                                   TAPI_MCAST_ADDR_ALL_ROUTERS,
                                   src_addr, eth_src);
    if (rc != 0)
        return rc;

    rc = tapi_tad_trsend_start(ta_name, session, csap,
                               pkt_tmpl, RCF_MODE_BLOCKING);

    asn_free_value(pkt_tmpl);

    return rc;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp2_ip4_eth_send_query(const char    *ta_name,
                              int            session,
                              csap_handle_t  csap,
                              int            max_resp_time,
                              in_addr_t      group_addr,
                              in_addr_t      src_addr,
                              bool skip_eth,
                              uint8_t       *eth_src)
{
    te_errno   rc       = 0;
    asn_value *pkt_tmpl = NULL;

    /* Add IGMPv2 layer message to PDU template/pattern */
    rc = tapi_igmp2_add_pdu(&pkt_tmpl, NULL, false,
                            TAPI_IGMP_TYPE_QUERY,
                            max_resp_time, group_addr);
    if (rc != 0)
        return rc;

    /* Add IPv4 layer header to PDU template/pattern */
    if (skip_eth)
    {
        rc = tapi_igmp_add_ip4_pdu(&pkt_tmpl, NULL, false,
                                   group_addr, src_addr);
    }
    else
    {
        rc = tapi_igmp_add_ip4_eth_pdu(&pkt_tmpl, NULL, false,
                                       group_addr, src_addr, eth_src);
    }
    if (rc != 0)
        return rc;

    rc = tapi_tad_trsend_start(ta_name, session, csap,
                               pkt_tmpl, RCF_MODE_BLOCKING);

    asn_free_value(pkt_tmpl);

    return rc;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_add_report_pdu(asn_value               **tmpl_or_ptrn,
                          asn_value               **pdu,
                          bool is_pattern,
                          tapi_igmp3_group_list_t  *group_list)
{
    asn_value *tmp_pdu;
    int        type = TAPI_IGMP3_TYPE_REPORT;

    CHECK_RC(tapi_tad_tmpl_ptrn_add_layer(tmpl_or_ptrn, is_pattern,
                                          ndn_igmp_message, "#igmp",
                                          &tmp_pdu));

    CHECK_RC(asn_write_int32(tmp_pdu, type, "type.#plain"));

    if (group_list != NULL)
    {
        uint8_t *data = NULL;
        int      data_len = 0;
        int      offset = 0;

        CHECK_RC(asn_write_int32(tmp_pdu, group_list->groups_no,
                                 "number-of-groups.#plain"));

        data_len = tapi_igmp3_group_list_length(group_list);
        data = TE_ALLOC(data_len);
        CHECK_RC(tapi_igmp3_group_list_gen_bin(group_list, data,
                                               data_len, &offset));
        CHECK_RC(asn_write_value_field(tmp_pdu, data, data_len,
                                       "group-record-list.#plain"));
        free(data);
    }
    else if (!is_pattern)
    {
        CHECK_RC(asn_write_int32(tmp_pdu, 0,
                                 "number-of-groups.#plain"));
#if 0
        CHECK_RC(asn_write_value_field(tmp_pdu, "", 0,
                                       "group-record-list.#plain"));
#endif
    }

    if (pdu != NULL)
        *pdu = tmp_pdu;

    return 0;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_ip4_eth_send_report(const char      *ta_name,
                               int              session,
                               csap_handle_t    csap,
                               tapi_igmp3_group_list_t  *group_list,
                               in_addr_t        src_addr,
                               uint8_t         *eth_src)
{
    te_errno       rc = 0;
    asn_value     *pkt_tmpl = NULL;

    rc = tapi_igmp3_add_report_pdu(&pkt_tmpl, NULL, false, group_list);
    if (rc != 0)
        return rc;

    /* Add IPv4 layer header to PDU template/pattern */
    rc = tapi_igmp_add_ip4_eth_pdu(&pkt_tmpl, NULL, false,
                                   TAPI_MCAST_ADDR_ALL_MCR,
                                   src_addr, eth_src);
    if (rc != 0)
        return rc;

    rc = tapi_tad_trsend_start(ta_name, session, csap,
                               pkt_tmpl, RCF_MODE_BLOCKING);

    asn_free_value(pkt_tmpl);

    return rc;
}


/* Threshold from which the exponential form of time representation is used */
#define IGMP3_TIME_EXPONENTIAL      128

/**
 * Convert encoded exponential timeout code to seconds.
 * See RFC 3376, section 4.1.1, 4.1.7.
 *
 * @param code  Time interval in exponential form.
 *
 * @return      Time interval in traditional linear representation.
 */
static unsigned
tapi_igmp3_code_to_time(uint8_t code)
{
    unsigned interval = 0;

    if (code < IGMP3_TIME_EXPONENTIAL)
    {
        interval = code;
    }
    else
    {
        uint8_t mant = code & 0x0f;
        uint8_t exp = (code & 0x70) >> 4;

        interval = (mant | 0x10) << (exp + 3);
    }

    return interval;
}

/**
 * Convert IGMPv3 time to exponential code.
 * See RFC 3376, section 4.1.1, 4.1.7.
 *
 * @param interval  Time interval in traditional linear representation:
 *                  - 1/10 second for Max Resp Code
 *                  - seconds for Querier's Query Interval Code
 *
 * @return          Time interval in exponential form suitable for
 *                  Max Resp Code field and
 *                  QQIC (Querier's Query Interval Code) field
 *                  of IGMPv3 Query message.
 */
static uint8_t
tapi_igmp3_time_to_code(unsigned interval)
{
    const uint8_t mant_max = 0x0f;
    const uint8_t exp_min  = 0;
    const uint8_t exp_max  = 0x07;
    unsigned      mant     = 0;
    uint8_t       exp      = 0;
    uint8_t       code     = 0;


    if (interval < IGMP3_TIME_EXPONENTIAL)
        return (uint8_t)interval;

    for (exp = exp_min; exp <= exp_max; exp++)
    {
        /* Round down time to represent in exponential form */
        mant = interval >> (exp + 3);
        if (mant <= (mant_max | 0x10))
            break;
    }
    mant &= mant_max;

    code = 0x80 | (exp << 4) | mant;

    return code;
}

#undef IGMP3_TIME_EXPONENTIAL

/* See the description in tapi_igmp.h */
uint8_t
tapi_igmp3_max_response_time_to_code(unsigned max_resp_time)
{
    /* Max Response Code represented in units of 1/10 second */
    return tapi_igmp3_time_to_code(max_resp_time * 10);
}

/* See the description in tapi_igmp.h */
unsigned
tapi_igmp3_max_response_code_to_time(uint8_t max_resp_code)
{
    /* Max Response Code represented in units of 1/10 second */
    return tapi_igmp3_code_to_time(max_resp_code) / 10;
}

/* See the description in tapi_igmp.h */
uint8_t
tapi_igmp3_qqi_to_qqic(unsigned qqi)
{
    return tapi_igmp3_time_to_code(qqi);
}

/* See the description in tapi_igmp.h */
unsigned
tapi_igmp3_qqic_to_qqi(uint8_t qqic)
{
    return tapi_igmp3_code_to_time(qqic);
}


/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_add_query_pdu(asn_value               **tmpl_or_ptrn,
                         asn_value               **pdu,
                         bool is_pattern,
                         int                       max_resp_code,
                         in_addr_t                 group_addr,
                         int                       s_flag,
                         int                       qrv,
                         int                       qqic,
                         tapi_igmp3_src_list_t    *src_list)
{
    asn_value *tmp_pdu;
    int        type = IGMP_HOST_MEMBERSHIP_QUERY;

    CHECK_RC(tapi_tad_tmpl_ptrn_add_layer(tmpl_or_ptrn, is_pattern,
                                          ndn_igmp_message, "#igmp",
                                          &tmp_pdu));

    CHECK_RC(asn_write_int32(tmp_pdu, type, "type.#plain"));

    if (max_resp_code >= 0)
        CHECK_RC(asn_write_int32(tmp_pdu, max_resp_code,
                                 "max-resp-time.#plain"));

    CHECK_RC(asn_write_value_field(tmp_pdu,
                                   &group_addr, sizeof(group_addr),
                                   "group-address.#plain"));

    CHECK_RC(asn_write_int32(tmp_pdu, s_flag, "s-flag.#plain"));
    CHECK_RC(asn_write_int32(tmp_pdu, qrv, "qrv.#plain"));
    CHECK_RC(asn_write_int32(tmp_pdu, qqic, "qqic.#plain"));

    if (src_list != NULL)
    {
        uint8_t *data = NULL;
        int      data_len = 0;
        int      offset = 0;

        CHECK_RC(asn_write_int32(tmp_pdu, src_list->src_no,
                             "number-of-sources.#plain"));

        data_len = tapi_igmp3_src_list_length(src_list);
        data = TE_ALLOC(data_len);
        CHECK_RC(tapi_igmp3_src_list_gen_bin(src_list, data, data_len, &offset));
        CHECK_RC(asn_write_value_field(tmp_pdu, data, data_len,
                                       "source-address-list.#plain"));
        free(data);
    }
    else
    if (!is_pattern)
    {
        CHECK_RC(asn_write_int32(tmp_pdu, 0,
                             "number-of-sources.#plain"));
#if 0
        CHECK_RC(asn_write_value_field(tmp_pdu, "", 0,
                                       "source-address-list.#plain"));
#endif
    }

    if (pdu != NULL)
        *pdu = tmp_pdu;

    return 0;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_ip4_eth_send_query(const char            *ta_name,
                              int                    session,
                              csap_handle_t          csap,
                              int                    max_resp_code,
                              in_addr_t              group_addr,
                              int                    s_flag,
                              int                    qrv,
                              int                    qqic,
                              tapi_igmp3_src_list_t *src_list,
                              in_addr_t              src_addr,
                              bool skip_eth,
                              uint8_t               *eth_src)
{
    te_errno       rc = 0;
    asn_value     *pkt_tmpl = NULL;
    in_addr_t      dst_addr = 0;

    rc = tapi_igmp3_add_query_pdu(&pkt_tmpl, NULL, false,
                                  max_resp_code, group_addr, s_flag,
                                  qrv, qqic, src_list);
    if (rc != 0)
        return rc;

    /* Add IPv4 layer header to PDU template/pattern */
    dst_addr =
        (group_addr == htonl(INADDR_ANY)) ? TAPI_MCAST_ADDR_ALL_HOSTS :
                                            group_addr;
    if (skip_eth)
    {
        rc = tapi_igmp_add_ip4_pdu(&pkt_tmpl, NULL, false,
                                   dst_addr,
                                   src_addr);
    }
    else
    {
        rc = tapi_igmp_add_ip4_eth_pdu(&pkt_tmpl, NULL, false,
                                       dst_addr,
                                       src_addr, eth_src);
    }
    if (rc != 0)
        return rc;

    rc = tapi_tad_trsend_start(ta_name, session, csap,
                               pkt_tmpl, RCF_MODE_BLOCKING);

    asn_free_value(pkt_tmpl);

    return rc;
}

/* See the description in tapi_igmp.h */
extern te_errno
tapi_igmp3_ip4_eth_send_query_default(const char            *ta_name,
                                      int                    session,
                                      csap_handle_t          csap,
                                      in_addr_t              group_addr,
                                      tapi_igmp3_src_list_t *src_list,
                                      in_addr_t              src_addr,
                                      bool skip_eth,
                                      uint8_t               *eth_src)
{
    return tapi_igmp3_ip4_eth_send_query(
        ta_name, session,
        csap,
        tapi_igmp3_max_response_time_to_code(
            TAPI_IGMP_QUERY_MAX_RESP_TIME_DEFAULT_S),
        group_addr,
        TAPI_IGMP3_QUERY_S_DEFAULT,
        TAPI_IGMP3_QUERY_QRV_DEFAULT,
        tapi_igmp3_qqi_to_qqic(TAPI_IGMP3_QUERY_QQI_DEFAULT_S),
        src_list,
        src_addr,
        skip_eth,
        eth_src);
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_src_list_init(tapi_igmp3_src_list_t *src_list)
{
#define IGMP3_SRC_LIST_PREALLOCATED_SIZE 16

    if (src_list == NULL)
        return TE_RC(TE_TAPI, TE_EINVAL);

    src_list->src_no = 0;
    src_list->src_no_max = IGMP3_SRC_LIST_PREALLOCATED_SIZE;
    src_list->src_addr = TE_ALLOC(sizeof(in_addr_t) * src_list->src_no_max);

    return 0;

#undef IGMP3_SRC_LIST_PREALLOCATED_SIZE
}

/* See the description in tapi_igmp.h */
void
tapi_igmp3_src_list_free(tapi_igmp3_src_list_t *src_list)
{
    if (src_list == NULL)
        return;
    if ((src_list->src_no_max > 0) && (src_list->src_addr != NULL))
    {
        free(src_list->src_addr);
        src_list->src_addr = NULL;
        src_list->src_no_max = 0;
        src_list->src_no = 0;
    }
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_src_list_add(tapi_igmp3_src_list_t *src_list, in_addr_t addr)
{
    in_addr_t *tmp_list;
    int        tmp_size;

    if ((src_list == NULL) ||
        (src_list->src_addr == NULL) ||
        (src_list->src_no_max <= 0) ||
        (src_list->src_no >= TAPI_IGMP3_SRC_LIST_SIZE_MAX))
    {
        return TE_RC(TE_TAPI, TE_EINVAL);
    }

    if (src_list->src_no >= src_list->src_no_max)
    {
        tmp_size = src_list->src_no_max * 2;
        assert(src_list->src_no < tmp_size);

        tmp_list = (in_addr_t *)realloc(src_list->src_addr,
                                        sizeof(in_addr_t *) * tmp_size);
        if (tmp_list == NULL)
            return TE_RC(TE_TAPI, TE_ENOMEM);
        src_list->src_addr = tmp_list;
        src_list->src_no_max = tmp_size;
    }

    src_list->src_addr[src_list->src_no++] = addr;

    return 0;
}

/* See the description in tapi_igmp.h */
int
tapi_igmp3_src_list_length(tapi_igmp3_src_list_t *src_list)
{
    return (src_list == NULL) ? 0 :
           src_list->src_no * sizeof(in_addr_t);
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_src_list_gen_bin(tapi_igmp3_src_list_t *src_list,
                                void *buf, int buf_size, int *offset)
{
    uint8_t *p = (uint8_t *)buf + *offset;
    int len = tapi_igmp3_src_list_length(src_list);

    if (src_list == NULL)
        return 0;

    if (buf_size - *offset < len)
        return TE_RC(TE_TAPI, TE_EINVAL);
    memcpy(p, src_list->src_addr, len);
    *offset += len;

    return 0;
}

/* See the description in tapi_igmp.h */
int
tapi_igmp3_group_record_length(tapi_igmp3_group_record_t *group_record)
{
    assert(group_record != NULL);
    return TAPI_IGMP3_GROUP_RECORD_HDR_LEN +
           tapi_igmp3_src_list_length(&group_record->src_list) +
           group_record->aux_data_len * sizeof(uint32_t);
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_group_record_gen_bin(tapi_igmp3_group_record_t *group_record,
                               void *buf, int buf_size, int *offset)
{
    uint16_t  tmp_src_no;
    uint8_t  *p;
    int       aux_len;
    te_errno  rc;

    assert(group_record != NULL);
    assert(buf != NULL);
    assert(offset != NULL);

    p = (uint8_t *)buf + *offset;
    if (buf_size - *offset < tapi_igmp3_group_record_length(group_record))
        return TE_RC(TE_TAPI, TE_EINVAL);

    /* Fill Record Type field */
    *p++ = (uint8_t)group_record->record_type;

    /* Fill Aux Data Len field */
    *p++ = (uint8_t)group_record->aux_data_len;

    /* Fill Number of Sources field */
    tmp_src_no = htons(group_record->src_list.src_no);
    memcpy(p, &tmp_src_no, sizeof(uint16_t));
    p += sizeof(uint16_t);

    *offset += sizeof(uint32_t);

    /* Fill Group Multicast Address field */
    memcpy(p, &group_record->group_address, sizeof(in_addr_t));
    *offset += sizeof(in_addr_t);

    if ((rc = tapi_igmp3_src_list_gen_bin(&group_record->src_list,
                                          buf, buf_size, offset)) != 0)
    {
        return rc;
    }

    /* Fill Auxiliary Data */
    aux_len = group_record->aux_data_len * sizeof(uint32_t);
    if (buf_size - *offset < aux_len)
        return TE_RC(TE_TAPI, TE_EINVAL);
    memcpy(buf + *offset, group_record->aux_data, aux_len);
    *offset += aux_len;

    return 0;
}

/* See the description in tapi_igmp.h */
int
tapi_igmp3_group_list_length(tapi_igmp3_group_list_t *group_list)
{
    int len = 0;
    int grp_no;

    for (grp_no = 0; grp_no < group_list->groups_no; grp_no++)
    {
        len += tapi_igmp3_group_record_length(group_list->groups[grp_no]);
    }
    return len;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_group_list_gen_bin(tapi_igmp3_group_list_t *group_list,
                             void *buf, int buf_size, int *offset)
{
    te_errno rc;
    int      grp_no;
    int      len;

    assert(group_list != NULL);
    assert(buf != NULL);
    assert(offset != NULL);

    len = tapi_igmp3_group_list_length(group_list);
    if (buf_size - *offset < len)
        return TE_RC(TE_TAPI, TE_EINVAL);

    for (grp_no = 0; grp_no < group_list->groups_no; grp_no++)
    {
        if ((rc = tapi_igmp3_group_record_gen_bin(group_list->groups[grp_no],
                                                  buf, buf_size,
                                                  offset)) != 0)
        {
            ERROR("Failed to pack group records to binary format");
            return rc;
        }
    }

    return 0;
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_group_record_init(tapi_igmp3_group_record_t *group_record,
                             int group_type, in_addr_t group_address,
                             void *aux_data, int aux_data_len)
{
    if ((group_record == NULL) ||
        ((aux_data_len > 0) && (aux_data == NULL)))
        return TE_RC(TE_TAPI, TE_EINVAL);

    group_record->record_type   = group_type;
    group_record->group_address = group_address;
    group_record->aux_data = aux_data;
    group_record->aux_data_len = aux_data_len;

    return tapi_igmp3_src_list_init(&group_record->src_list);
}

/* See the description in tapi_igmp.h */
void
tapi_igmp3_group_record_free(tapi_igmp3_group_record_t *group_record)
{
    if (group_record == NULL)
        return;

    if ((group_record->aux_data_len > 0) && (group_record->aux_data != NULL))
        free(group_record->aux_data);

    tapi_igmp3_src_list_free(&group_record->src_list);

    memset(group_record, 0, sizeof(tapi_igmp3_group_record_t));
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_group_record_add_source(tapi_igmp3_group_record_t *group_record,
                                  in_addr_t src_addr)
{
    if (group_record == NULL)
        return TE_RC(TE_TAPI, TE_EINVAL);

    return tapi_igmp3_src_list_add(&group_record->src_list, src_addr);
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_group_list_init(tapi_igmp3_group_list_t *group_list)
{
#define IGMP3_GROUP_LIST_PREALLOCATED_SIZE 16

    if (group_list == NULL)
        return TE_RC(TE_TAPI, TE_EINVAL);

    group_list->groups_no = 0;
    group_list->groups_no_max = IGMP3_GROUP_LIST_PREALLOCATED_SIZE;
    group_list->groups = TE_ALLOC(sizeof(tapi_igmp3_group_record_t *) *
                                  group_list->groups_no_max);

    return 0;

#undef IGMP3_GROUP_LIST_PREALLOCATED_SIZE
}

/* See the description in tapi_igmp.h */
void
tapi_igmp3_group_list_free(tapi_igmp3_group_list_t *group_list)
{
    if (group_list == NULL)
        return;
    if ((group_list->groups_no_max > 0) && (group_list->groups != NULL))
    {
        int grp_no;

        for (grp_no = 0; grp_no < group_list->groups_no; grp_no++)
        {
            tapi_igmp3_group_record_free(group_list->groups[grp_no]);
            free(group_list->groups[grp_no]);
        }

        free(group_list->groups);
        group_list->groups = NULL;
        group_list->groups_no_max = 0;
        group_list->groups_no = 0;
    }
}

/* See the description in tapi_igmp.h */
te_errno
tapi_igmp3_group_list_add(tapi_igmp3_group_list_t *group_list,
                          tapi_igmp3_group_record_t *group_record)
{
    tapi_igmp3_group_record_t **tmp_records;
    int                         tmp_size;

    if ((group_list == NULL) ||
        (group_list->groups == NULL) ||
        (group_list->groups_no_max <= 0) ||
        (group_list->groups_no >= TAPI_IGMP3_GROUP_LIST_SIZE_MAX))
    {
        return TE_RC(TE_TAPI, TE_EINVAL);
    }

    if (group_list->groups_no >= group_list->groups_no_max)
    {
        tmp_size = group_list->groups_no_max * 2;
        assert(group_list->groups_no < tmp_size);

        tmp_records = realloc(group_list->groups,
                              tmp_size * sizeof(tapi_igmp3_group_record_t *));
        if (tmp_records == NULL)
            return TE_RC(TE_TAPI, TE_ENOMEM);
        group_list->groups = tmp_records;
        group_list->groups_no_max = tmp_size;
    }

    group_list->groups[group_list->groups_no++] = group_record;

    return 0;
}


/* See the description in tapi_igmp.h */
tapi_igmp3_src_list_t *
tapi_igmp3_src_list_new(tapi_igmp3_src_list_t *src_list, ...)
{
    in_addr_t src;
    va_list ap;

    if (src_list == NULL)
    {
        src_list = TE_ALLOC(sizeof(tapi_igmp3_src_list_t));
        if (tapi_igmp3_src_list_init(src_list) != 0)
            TEST_FAIL("Canot initialise group records list structure");
    }

    va_start(ap, src_list);
    while ((src = va_arg(ap, in_addr_t)) != 0)
    {
        if (tapi_igmp3_src_list_add(src_list, src) != 0)
            TEST_FAIL("Failed to add source address to the list");
    }
    va_end(ap);

    return src_list;
}


/* See the description in tapi_igmp.h */
tapi_igmp3_group_record_t *
tapi_igmp3_group_record_new(tapi_igmp3_group_record_t *group_record,
                            int group_type, in_addr_t group_address,
                            void *aux_data, int aux_data_len, ...)
{
    in_addr_t src;
    va_list ap;

    if (group_record == NULL)
    {
        group_record = TE_ALLOC(sizeof(tapi_igmp3_group_record_t));
        if (tapi_igmp3_group_record_init(group_record, group_type, group_address,
                                         aux_data, aux_data_len) != 0)
            TEST_FAIL("Canot initialise group record structure");
    }

    va_start(ap, aux_data_len);
    while ((src = va_arg(ap, in_addr_t)) != 0)
    {
        if (tapi_igmp3_group_record_add_source(group_record, src) != 0)
            TEST_FAIL("Failed to add source address to group record");
    }
    va_end(ap);

    return group_record;
}

/* See the description in tapi_igmp.h */
tapi_igmp3_group_list_t *
tapi_igmp3_group_list_new(tapi_igmp3_group_list_t *group_list, ...)
{
    tapi_igmp3_group_record_t *group_record = NULL;
    va_list ap;

    if (group_list == NULL)
    {
        group_list = TE_ALLOC(sizeof(tapi_igmp3_group_list_t));
        if (tapi_igmp3_group_list_init(group_list) != 0)
            TEST_FAIL("Canot initialise group records list structure");
    }

    va_start(ap, group_list);
    while ((group_record = va_arg(ap, tapi_igmp3_group_record_t *)) != NULL)
    {
        if (tapi_igmp3_group_list_add(group_list, group_record) != 0)
            TEST_FAIL("Failed to add group record to the list");
    }
    va_end(ap);

    return group_list;
}
