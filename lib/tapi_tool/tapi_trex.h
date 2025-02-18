/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (C) 2023-2024 OKTET Labs Ltd. All rights reserved. */
/** @file
 * @brief TAPI to manage Cisco TRex
 *
 * @defgroup tapi_trex TAPI to manage Cisco TRex
 * @ingroup te_ts_tapi
 * @{
 *
 * TAPI to manage *Cisco TRex*.
 */

#ifndef __TE_TAPI_TREX_H__
#define __TE_TAPI_TREX_H__

#include <sys/socket.h>

#include "te_errno.h"
#include "tapi_job_opt.h"
#include "tapi_job.h"

#include "rcf_rpc.h"

#ifdef __cplusplus
extern "C" {
#endif

/** TRex default client payload. */
#define TAPI_TREX_DEFAULT_CLIENT_HTTP_PAYLOAD "GET /3384 HTTP/1.1\nHo"

/** TRex default server payload. */
#define TAPI_TREX_DEFAULT_SERVER_HTTP_PAYLOAD "HTTP/1.1 200 OK\nServe"

/**
 * @name Macros to setup @p tapi_trex_opt::clients and @p tapi_trex_opt::servers
 *
 * These macros simplify configuration of Cisco TRex clients and servers,
 * help with substitution of the correct interface name.
 *
 * @{
 */

/**
 * Set linux interface for TRex without binding.
 *
 * @code{.c}
 * tapi_trex_opt trex_opt;
 * trex_opt.servers = TAPI_TREX_SERVERS(
 *      TAPI_TREX_SERVER(
 *          .common.interface = TAPI_TREX_LINUX_IFACE("Agt_A", "eth0"),
 *          ...
 *      ));
 * @endcode
 */
#define TAPI_TREX_LINUX_IFACE(ta_, iface_) \
    tapi_trex_interface_init_oid(true, "/agent:%s/interface:%s", \
                                 (ta_), (iface_))

/**
 * Set linux interface for TRex with binding.
 *
 * @code{.c}
 * tapi_trex_opt trex_opt;
 * trex_opt.clients = TAPI_TREX_CLIENTS(
 *      TAPI_TREX_CLIENT(
 *          .common.interface = TAPI_TREX_PCI_BY_IFACE("Agt_A", "eth0"),
 *          ...
 *      ));
 * @endcode
 */
#define TAPI_TREX_PCI_BY_IFACE(ta_, iface_) \
    tapi_trex_interface_init_oid(false, "/agent:%s/interface:%s", \
                                 (ta_), (iface_))

/**
 * Set the PCI address interface for TRex with binding.
 *
 * @code{.c}
 * tapi_trex_opt trex_opt;
 * trex_opt.clients = TAPI_TREX_CLIENTS(
 *      TAPI_TREX_CLIENT(
 *          .common.interface = TAPI_TREX_PCI_BY_BDF("Agt_A",
 *                                                   "0000:00:04.0"),
 *          ...
 *      ));
 * @endcode
 */
#define TAPI_TREX_PCI_BY_BDF(ta_, addr_) \
    tapi_trex_interface_init_oid(false, "/agent:%s/hardware:/pci:/device:%s", \
                                 (ta_), (addr_))

/**
 * Convenience TRex clients vector constructor.
 *
 * @code{.c}
 * tapi_trex_opt trex_opt;
 * trex_opt.clients = TAPI_TREX_CLIENTS(
 *     TAPI_TREX_CLIENT(
 *         .common.interface = TAPI_TREX_PCI_BY_IFACE("Agt_A", "eth0"),
 *         .common.port = 80,
 *         .common.payload = "GET /3384 HTTP/1.1\r\nHo"
 * ));
 * @endcode
 */
#define TAPI_TREX_CLIENTS(...) \
    ((tapi_trex_client_config *[])              \
        {                                       \
            __VA_ARGS__,                        \
            NULL                                \
        }                                       \
    )

/**
 * Convenience TRex client constructor.
 *
 * @sa TAPI_TREX_CLIENTS
*/
#define TAPI_TREX_CLIENT(...) \
    (&(tapi_trex_client_config) { __VA_ARGS__ })

/**
 * Convenience TRex servers vector constructor.
 *
 * @code{.c}
 * tapi_trex_opt trex_opt;
 * trex_opt.servers = TAPI_TREX_SERVERS(
 *   TAPI_TREX_SERVER(
 *    .common.interface = TAPI_TREX_PCI_BY_IFACE("Agt_A", "eth0"),
 *    .common.payload = "HTTP/1.1 200 OK\r\n"
 *        "Content-Type: text/html\r\nConnection: keep-alive\r\n"
 *        "Content-Length: 18\r\n\r\n<html>Hello</html>"
 * ));
 * @endcode
 */

#define TAPI_TREX_SERVERS(...) \
    ((tapi_trex_server_config *[])              \
        {                                       \
            __VA_ARGS__,                        \
            NULL                                \
        }                                       \
    )

/**
 * Convenience TRex server constructor.
 *
 * @sa TAPI_TREX_SERVERS
 */
#define TAPI_TREX_SERVER(...) \
    (&(tapi_trex_server_config) { __VA_ARGS__ })

/**@}*/

/** List of parameters in per port statistics. */
typedef enum tapi_trex_port_stat_enum {
    TAPI_TREX_PORT_STAT_OPKTS = 0,
    TAPI_TREX_PORT_STAT_OBYTES,
    TAPI_TREX_PORT_STAT_IPKTS,
    TAPI_TREX_PORT_STAT_IBYTES,
    TAPI_TREX_PORT_STAT_IERRS,
    TAPI_TREX_PORT_STAT_OERRS,
    TAPI_TREX_PORT_STAT_CURRENT_TIME,
    TAPI_TREX_PORT_STAT_TEST_DURATION,
} tapi_trex_port_stat_enum;

/** List of parameters in global statistics. */
typedef enum tapi_trex_global_stat_enum {
    TAPI_TREX_GLOBAL_STAT_CURRENT_TIME = 0,
    TAPI_TREX_GLOBAL_STAT_TEST_DURATION,
    TAPI_TREX_GLOBAL_STAT_TOTAL_TX,
    TAPI_TREX_GLOBAL_STAT_TOTAL_RX,
    TAPI_TREX_GLOBAL_STAT_TOTAL_PPS,
    TAPI_TREX_GLOBAL_STAT_TOTAL_CPS,
    TAPI_TREX_GLOBAL_STAT_EXPECTED_PPS,
    TAPI_TREX_GLOBAL_STAT_EXPECTED_CPS,
    TAPI_TREX_GLOBAL_STAT_EXPECTED_L7_BPS,
} tapi_trex_global_stat_enum;

/** TRex port stat filter. */
typedef struct tapi_trex_port_stat_flt {
    /* Single port stat filter */
    tapi_job_channel_t *filter;
    /** Port stat param. */
    tapi_trex_port_stat_enum param;
    /** Index of the port. */
    unsigned int index;
} tapi_trex_port_stat_flt;

/** TRex per port stat filters. */
typedef struct tapi_trex_per_port_stat_flts {
    /** List of port stat filters (@c NULL terminated). */
    tapi_trex_port_stat_flt **flts;
    /** Number of port used in filters. */
    unsigned int n_ports;
} tapi_trex_per_port_stat_flts;

/** Global stat filter. */
typedef struct tapi_trex_global_stat_flt {
    /* Single global stat filter */
    tapi_job_channel_t *filter;
    /** Global stat param. */
    tapi_trex_global_stat_enum param;
} tapi_trex_global_stat_flt;

/** TRex statistics for a single port. */
typedef struct tapi_trex_port_stat {
    uint64_t opackets;
    uint64_t obytes;
    uint64_t ipackets;
    uint64_t ibytes;
    uint64_t ierrors;
    uint64_t oerrors;
    double curr_time;
    double test_duration;
} tapi_trex_port_stat;

/** TRex global statistics. */
typedef struct tapi_trex_global_stat {
    double total_tx;
    double total_rx;
    double total_pps;
    double total_cps;
    double expected_pps;
    double expected_cps;
    double expected_l7_bps;
    double curr_time;
    double test_duration;
    bool valid;
} tapi_trex_global_stat;

/** TRex per-port statistics. */
typedef struct tapi_trex_per_port_stat {
    /** Per port statistics (@c NULL terminated list). */
    tapi_trex_port_stat **ports;
    /** Number of ports in each item. */
    unsigned int n_ports;
} tapi_trex_per_port_stat;

/** TRex one optional filter. */
typedef struct tapi_trex_opt_flt {
    tapi_job_channel_t *cl_flt;
    tapi_job_channel_t *srv_flt;
} tapi_trex_opt_flt;

/** TRex tool information. */
typedef struct tapi_trex_app {
    /** TAPI job handle. */
    tapi_job_t *job;
    /** Output channel handles. */
    tapi_job_channel_t *out_chs[2];
    /** Command line used to start the TRex job. */
    te_vec cmd;
    /** Filters list: */
    /** TRex stdout content. */
    tapi_job_channel_t *std_out;
    /** TRex stderr content. */
    tapi_job_channel_t *std_err;
    /** Total-Tx filter. */
    tapi_job_channel_t *total_tx_filter;
    /** Total-Rx filter. */
    tapi_job_channel_t *total_rx_filter;
    /** Total-CPS filter. */
    tapi_job_channel_t *total_cps_filter;
    /** Total-tx-pkt filter. */
    tapi_job_channel_t *total_tx_pkt_filter;
    /** Total-rx-pkt filter. */
    tapi_job_channel_t *total_rx_pkt_filter;
    /** m_traffic_duration client filter. */
    tapi_job_channel_t *m_traff_dur_cl_flt;
    /** m_traffic_duration server filter. */
    tapi_job_channel_t *m_traff_dur_srv_flt;

    /** total-tx-bytes filter. */
    tapi_job_channel_t *total_tx_bytes_flt;
    /** total-rx-bytes filter. */
    tapi_job_channel_t *total_rx_bytes_flt;

    /** Optional filters. */
    tapi_trex_opt_flt *opt_flts;

    /** Per port stat filters */
    tapi_trex_per_port_stat_flts per_port_stat_flts;

    /** List of global stat filters (@c NULL terminated). */
    tapi_trex_global_stat_flt *global_stat_flts;
} tapi_trex_app;

/** Representation of possible values for tapi_trex_opt::verbose option. */
typedef enum tapi_trex_verbose {
    /** Option is omitted */
    TAPI_TREX_VERBOSE_NONE = TAPI_JOB_OPT_ENUM_UNDEF,
    /** Shows debug info on startup. */
    TAPI_TREX_VERBOSE_MODE_MIN,
    /** Shows debug info during run. */
    TAPI_TREX_VERBOSE_MODE_MAX,
} tapi_trex_verbose_t;

/** Representation of possible values for tapi_trex_opt::iom option. */
typedef enum tapi_trex_iom {
    /** Option is omitted */
    TAPI_TREX_IOM_NONE = TAPI_JOB_OPT_ENUM_UNDEF,
    /** IO mode for server output: silent. */
    TAPI_TREX_IOM_SILENT = 0,
    /** IO mode for server output: normal. */
    TAPI_TREX_IOM_NORMAL,
    /** IO mode for server output: short. */
    TAPI_TREX_IOM_SHORT,
} tapi_trex_iom_t;

/** Representation of possible values for tapi_trex_opt::*-so options. */
typedef enum tapi_trex_so {
    /** Option is omitted */
    TAPI_TREX_SO_NONE = TAPI_JOB_OPT_ENUM_UNDEF,
    /** mlx4 share object should be loaded. */
    TAPI_TREX_SO_MLX4 = 0,
    /** mlx5 share object should be loaded */
    TAPI_TREX_SO_MLX5,
    /** Both mlx4/mlx5 share object should be loaded. */
    TAPI_TREX_SO_MLX4_MLX5,
    /** Napatech 3GD should be running. */
    TAPI_TREX_SO_NTACC,
    /** bnxt share object should be loaded */
    TAPI_TREX_SO_BNXT,
} tapi_trex_so_t;

/** TRex interface description. */
typedef struct tapi_trex_interface tapi_trex_interface;

/** Common TRex client/server options. */
typedef struct tapi_trex_common_config {
    /** IP range begin (if @c NULL then @c "0.0.0.0"). */
    const struct sockaddr *ip_range_beg;
    /** IP range end (if @c NULL then @c "0.0.0.0"). */
    const struct sockaddr *ip_range_end;
    /** Offset to add per port pair (if @c NULL then @c "0.0.0.0"). */
    const struct sockaddr *ip_offset;
    /** Port number in clients requests (if not set then @c 80). */
    tapi_job_opt_uint_t port;
    /** HTTP buffer to send to the other side. */
    const char *payload;
    /** Interface to use. */
    tapi_trex_interface *interface;
    /**
     * Real IP (or MAC) address of interface,
     * if @c NULL then @c "0.0.0.0".
     */
    const struct sockaddr *ip;
    /**
     * Real gateway IP (or MAC) address of interface,
     * if @c NULL then @c "0.0.0.0".
     */
    const struct sockaddr *gw;
} tapi_trex_common_config;

/** Specific TRex client options. */
typedef struct tapi_trex_client_config {
    tapi_trex_common_config common;
} tapi_trex_client_config;

/** Specific TRex server options. */
typedef struct tapi_trex_server_config {
    tapi_trex_common_config common;
} tapi_trex_server_config;

/** Default TRex client options initializer. */
extern const tapi_trex_client_config tapi_trex_client_config_default;

/** Default TRex server options initializer. */
extern const tapi_trex_server_config tapi_trex_server_config_default;

/**
 * Specific TRex options.
 *
 * Before starting tapi_trex it is necessary to initialize its options
 * @p tapi_trex_opt and call tapi_trex_create() to create configuration files
 * and properly bind PCI functions (if DPDK is used).
 *
 * Base @p tapi_trex_opt example:
 *
 * @code{.c}
 * tapi_trex_opt trex_opt = tapi_trex_default_opt;
 *
 * trex_opt.astf_template = getenv("TE_TREX_ASTF_TEMPLATE");
 * trex_opt.trex_exec = getenv("TE_TREX_EXEC");
 * trex_opt.force_close_at_end = true;
 * trex_opt.no_monitors = true;
 * trex_opt.lro_disable = true;
 *
 * // Setup servers
 * trex_opt.servers = TAPI_TREX_SERVERS(
 *    TAPI_TREX_SERVER(
 *        .common.interface = TAPI_TREX_PCI_BY_IFACE("Agt_A", "eth0"),
 *        .common.ip = agtA_addr,
 *        .common.gw = agtB_addr,
 *        .common.ip_range_beg = agtA_addr,
 *        .common.ip_range_end = agtA_addr,
 *        .common.payload = "HTTP/1.1 200 OK\r\n"
 *                "Content-Type: text/html\r\nConnection: keep-alive\r\n"
 *                "Content-Length: 18\r\n\r\n<html>Hello</html>"
 * ));
 *
 * // Setup clients
 * trex_opt.clients = ...;
 * @endcode
 */
typedef struct tapi_trex_opt {
    /**
     * @name TRex options
     * @{
     */
    /**
     * Standard output logging level (default is @c TE_LL_RING).
     */
    te_log_level stdout_log_level;
    /**
     * Standard error logging level (default is @c TE_LL_WARN).
     */
    te_log_level stderr_log_level;
    /**
     * If set, only server side ports (e.g. @c 1, @c 3 and etc.) are enabled
     * with ASTF service. Traffic won't be transmitted on clients ports.
     */
    bool astf_server_only;
    /**
     * Number of hardware threads to allocate for each port pair.
     * Overrides the @c 'c' argument from config file.
     */
    tapi_job_opt_uint_t n_threads;
    /** If set, disable TSO (advanced TCP mode). */
    bool tso_disable;
    /** If set, disable LRO (advanced TCP mode). */
    bool lro_disable;
    /**
     * Duration of the test, in seconds.
     *
     * @sa tapi_trex_opt::force_close_at_end option.
     */
    tapi_job_opt_double_t duration;
    /**
     * If set, each flow will be sent both from client to server and
     * server to client. It can achieve better port utilization when
     * flow traffic is asymmetric.
     */
    bool asymmetric_traffic_flow;
    /** If set, report latency using high dynamic range histograms. */
    bool use_hdr_histograms;
    /** If set, work in IPv6 mode. */
    bool ipv6;
    /**
     * Rate multiplier.
     * Multiply basic rate of templates by this number.
     */
    tapi_job_opt_double_t rate_multiplier;
    /** If set, won't wait for all flows to be closed, before terminating. */
    bool force_close_at_end;
    /**
     * If set, enable flow-control.
     * By default TRex disables flow-control.
     * If this option is given, it does not touch it
     */
    bool enable_flow_control;
    /** If set, disable watchdog. */
    bool no_watchdog;
    /** If set, run TRex DP/RX cores in realtime priority. */
    bool use_realtime_prio;
    /** If set, disable monitors publishers. */
    bool no_monitors;
    /** If set, don't retry to send packets on failure (queue full etc.). */
    bool dont_resend_pkts;
    /**
     * If set, use sleeps instead of busy wait in scheduler.
     * Less accurate, more power saving.
     */
    bool use_sleep;
    /** The higher the value, print more debug information. */
    tapi_trex_verbose_t verbose;
    /** IO mode for server output.*/
    tapi_trex_iom_t iom;
    /** Activate one of the --*-so options.*/
    tapi_trex_so_t so;
    /** Wait a few seconds between init of interfaces and sending traffic. */
    tapi_job_opt_uint_t init_wait_sec;
    /**
     * For running multi TRex instances on the same machine.
     * Each instance should have different name.
     */
    const char *instance_prefix;
    /** @} */

    /**
     * TRex client configurations list.
     * Like @c tapi_trex_client_config*[]. Should end with @c NULL.
     */
    tapi_trex_client_config **clients;
    /**
     * TRex server configurations list.
     * Like @c tapi_trex_server_config*[]. Should end with @c NULL.
     */
    tapi_trex_server_config **servers;

    /**
     * TRex configuration template.
     *
     * If @c NULL, the template from this example will be used:
     * @code{.yaml}
     *
     * - port_limit      : ${#IFACES}\n"
     *   version         : 2\n"
     *   interfaces: [${IFACES[, ]}]\n"
     *   port_info:\n"
     * ${PORTINFO_IP*    - ip${COLON} ${PORTINFO_IP[${}]}\n"
     *       default_gw${COLON} ${PORTINFO_DEFAULT_GW[${}]}\n}"
     * ${PORTINFO_DST_MAC*    - dest_mac${COLON} ${PORTINFO_DST_MAC[${}]}\n"
     *       src_mac${COLON} ${PORTINFO_SRC_MAC[${}]}\n}";
     *
     * @endcode
     */
    const char *cfg_template;

    /**
     * Extensions for @p tapi_trex_opt::astf_template.
     * You can replace some fields with TAPI TRex environment variables.
     *
     * @warning The following field names are currently reserved and
     *          it's not recommended to use them in this option:
     *  - @c CLIENT_HTTP
     *  - @c SERVER_HTTP
     *  - @c CLIENT_IP_START
     *  - @c CLIENT_IP_START
     *  - @c CLIENT_IP_END
     *  - @c CLIENT_IP_OFFSET
     *  - @c SERVER_IP_START
     *  - @c SERVER_IP_END
     *  - @c SERVER_IP_OFFSET
     *  - @c CLIENT_IP_PORT
     *  - @c SERVER_IP_PORT
     *
     * @sa tapi_trex_opt::astf_template
     */
    const te_kvpair_h *astf_vars;

    /**
     * Driver name for DPDK binding.
     * Should be @c NULL if interface is already bound.
     */
    const char *driver;
    /**
     * TRex ASTF template.
     *
     * Now TAPI TRex supports only JSON profile templates.
     * To create JSON profile template you need to use existing
     * Python traffic profile and use this command to see JSON profile:
     *
     * @code{.sh}
     * ./astf-sim -f <your_profile>.py --json
     * @endcode
     *
     * Example:
     *
     * @code{.sh}
     * ./astf-sim -f astf/http_simple.py --json
     * @endcode
     *
     * Use this JSON profile to create TAPI TRex ASTF template
     * (@p tapi_trex_opt::astf_template). You can replace some fields with
     * TAPI TRex environment variables using @p tapi_trex_opt::extensions.
     *
     * Fields usage see @p te_string_expand_kvpairs for more details.
     *
     * Example of JSON profile template:
     *
     * @code{.json}
     * {
     *    "buf_list": [
     *        "${CLIENT_HTTP[0]|base64uri}",
     *        "${SERVER_HTTP[0]|base64uri}"
     *    ],
     *
     *    "ip_gen_dist_list": [
     *        {
     *            "ip_start": "${CLIENT_IP_START[0]:-0.0.0.0}",
     *            "ip_end": "${CLIENT_IP_END[0]:-0.0.0.0}",
     *            "distribution": "seq",
     *            "dir": "c",
     *            "ip_offset": "${CLIENT_IP_OFFSET[0]:-0.0.0.0}"
     *        },
     *        {
     *            "ip_start": "${SERVER_IP_START[0]:-0.0.0.0}",
     *            "ip_end": "${SERVER_IP_END[0]:-0.0.0.0}",
     *            "distribution": "seq",
     *            "dir": "s",
     *            "ip_offset": "${SERVER_IP_OFFSET[0]:-0.0.0.0}"
     *        }
     *    ],
     *
     *    "program_list": [
     *        {
     *            "commands": [
     *                {
     *                    "name": "connect"
     *                },
     *                {
     *                    "name": "tx",
     *                    "buf_index": 0
     *                },
     *                {
     *                    "name": "rx",
     *                    "min_bytes": 10
     *                },
     *                {
     *                    "name": "delay",
     *                    "usec": 1000
     *                }
     *            ]
     *        },
     *        {
     *            "commands": [
     *                {
     *                    "name": "connect"
     *                },
     *                {
     *                    "name": "rx",
     *                    "min_bytes": 10
     *                },
     *                {
     *                    "name": "tx",
     *                    "buf_index": 1
     *                }
     *            ]
     *        }
     *    ],
     *
     *    "templates": [
     *        {
     *            "client_template": {
     *                "program_index": 0,
     *                "ip_gen": {
     *
     *                    "dist_client": {
     *                        "index": 0
     *                    },
     *
     *                    "dist_server": {
     *                        "index": 1
     *                    }
     *                },
     *
     *                "cluster": {},
     *                "port": ${CLIENT_IP_PORT[0]:-80},
     *                "cps": 1
     *            },
     *
     *            "server_template": {
     *                "program_index": 1,
     *                "assoc": [
     *                    {
     *                        "port": ${SERVER_IP_PORT[0]:-80}
     *                    }
     *                ]
     *            }
     *        }
     *    ],
     *
     *    "tg_names": []
     * }
     * @endcode
     *
     * @sa tapi_trex_opt::astf_vars
     */
    const char *astf_template;
    /**
     * Full path to TRex exec (should not be @c NULL).
     * The directory with TRex exec should also contain @c "astf_schema.json".
    */
    const char *trex_exec;
} tapi_trex_opt;

/** Default TRex options initializer. */
extern const tapi_trex_opt tapi_trex_default_opt;

/** TRex one optional filter values. */
typedef struct tapi_trex_opt_flt_vals {
    uint64_t cl_val;
    uint64_t srv_val;
} tapi_trex_opt_flt_vals;

/** TRex information from the stdout. */
typedef struct tapi_trex_report {
    /** Average Tx per second, bps. */
    double avg_tx;
    /** Average Rx per second, bps. */
    double avg_rx;
    /** Average connections per second, cps. */
    double avg_cps;
    /** Total tx packets. */
    uint64_t tx_pkts;
    /** Total rx packets. */
    uint64_t rx_pkts;
    /** Diration of client traffic, sec. */
    double m_traff_dur_cl;
    /** Diration of server traffic, sec. */
    double m_traff_dur_srv;

    /** Total bytes sent. */
    uint64_t total_tx_bytes;
    /** Total bytes received. */
    uint64_t total_rx_bytes;

    /** Optional filter values. */
    tapi_trex_opt_flt_vals *opt_flts_vals;
    /** Per port statistics. */
    tapi_trex_per_port_stat per_port_stat;
    /** Global statistics */
    tapi_trex_global_stat *global_stat;
} tapi_trex_report;


/**
 * Create @p tapi_trex_interface with PCI address (e.g. @c "0000:00:04.0").
 *
 * @param[in] use_kernel_interface  Use kernel or DPDK interface.
 * @param[in] oid_fmt               OID format string.
 * @param[in] ...                   Arguments for the format string.
 *
 * @return Allocated @p tapi_trex_interface structure.
 *
 * @code{.c}
 * tapi_trex_interface *iface = tapi_trex_interface_init_oid(
 *          false, "/agent:%s/interface:%s", "Agt_A", "eth0");
 * ...
 * tapi_trex_interface_free(iface);
 * @endcode
 *
 * @note Function result should be tapi_trex_interface_free()'d.
 *
 * @note If @p use_kernel_interface is @c true, then only @c '/agent/interface'
 *       OIDs are supported and the name of the interface is used.
 *       If @p use_kernel_interface is @c false, then OIDs are resolved
 *       to a PCI address.
 *
 * @note OID can be one the following:
 *          - @c '/agent/hardware/pci/vendor/device/instance'
 *          - @c '/agent/hardware/pci/device'
 *          - @c '/agent/interface'
 */
extern tapi_trex_interface *tapi_trex_interface_init_oid(
                                                bool use_kernel_interface,
                                                const char *oid_fmt,
                                                ...);

/**
 * Free allocated @p tapi_trex_interface.
 *
 * @param[in] interface     TAPI TRex interface.
 */
extern void tapi_trex_interface_free(tapi_trex_interface *interface);

/**
 * @name Create and run TAPI TRex instance
 *
 * One server run (no clients)
 * -------------------------------------------------
 *
 * @code{.c}
 * rcf_rpc_server *pcoA = ...;
 * tapi_job_factory_t *factoryA = NULL;
 *
 * tapi_trex_app *trex_app = NULL;
 * tapi_trex_opt trex_opt = tapi_trex_default_opt;
 * tapi_trex_report trex_report = { 0 };
 *
 * CHECK_RC(tapi_job_factory_rpc_create(pcoA, &factoryA));
 *
 * trex_opt.servers = TAPI_TREX_SERVERS(
 *  TAPI_TREX_SERVER(
 *      .common.interface = TAPI_TREX_PCI_BY_IFACE(pcoA->ta, "eth0"),
 *      .common.ip = "192.0.0.1",
 *      .common.gw = "192.0.0.2",
 *      .common.ip_range_beg = "192.0.0.1",
 *      .common.ip_range_end = "192.0.0.1",
 *      .common.payload = "HTTP/1.1 200 OK\r\n"
 *              "Content-Type: text/html\r\nConnection: keep-alive\r\n"
 *              "Content-Length: 18\r\n\r\n<html>Hello</html>"
 * ));
 *
 * CHECK_RC(tapi_trex_create(factoryA, &trex_opt, &trex_app));
 * CHECK_RC(tapi_trex_start(trex_app));
 * CHECK_RC(tapi_trex_wait(trex_app, -1));
 * CHECK_RC(tapi_trex_stop(trex_app));
 *
 * // Get and print report
 * CHECK_RC(tapi_trex_get_report(trex_app, &trex_report));
 * CHECK_RC(tapi_trex_report_mi_log(&trex_report));
 *
 * // Destroy TAPI TRex job
 * CHECK_RC(tapi_trex_destroy(pcoA->ta, trex_app, &trex_opt));
 * CHECK_RC(tapi_trex_destroy_report(&trex_report));
 * tapi_job_factory_destroy(factoryA);
 * @endcode
 *
 * One client run (no server ports)
 * -------------------------------------------------
 *
 * @code{.c}
 * rcf_rpc_server *pcoA = ...;
 * tapi_job_factory_t *factoryA = NULL;
 *
 * tapi_trex_app *trex_app = NULL;
 * tapi_trex_opt trex_opt = tapi_trex_default_opt;
 * tapi_trex_report trex_report = { 0 };
 *
 * CHECK_RC(tapi_job_factory_rpc_create(pcoA, &factoryA));
 *
 * trex_opt.clients = TAPI_TREX_CLIENTS(
 *  TAPI_TREX_CLIENT(
 *      .common.interface = TAPI_TREX_PCI_BY_IFACE(pcoA->ta, "eth0"),
 *      .common.ip = "192.0.0.1",
 *      .common.gw = "192.0.0.2",
 *      .common.ip_range_beg = "192.0.0.1",
 *      .common.ip_range_end = "192.0.0.1",
 *      .common.payload = "GET /3384 HTTP/1.1\r\nHo"
 * ));
 *
 * trex_opt.servers = TAPI_TREX_SERVERS(
 *  TAPI_TREX_SERVER(
 *      .common.ip = "192.0.0.1",
 *      .common.gw = "192.0.0.2",
 *      .common.ip_range_beg = "192.0.0.2",
 *      .common.ip_range_end = "192.0.0.2"
 * ));
 *
 * CHECK_RC(tapi_trex_create(factoryA, &trex_opt, &trex_app));
 * CHECK_RC(tapi_trex_start(trex_app));
 * CHECK_RC(tapi_trex_wait(trex_app, -1));
 * CHECK_RC(tapi_trex_stop(trex_app));
 *
 * // Get and print report
 * CHECK_RC(tapi_trex_get_report(trex_app, &trex_report));
 * CHECK_RC(tapi_trex_report_mi_log(&trex_report));
 *
 * // Destroy TAPI TRex job
 * CHECK_RC(tapi_trex_destroy(pcoA->ta, trex_app, &trex_opt));
 * CHECK_RC(tapi_trex_destroy_report(&trex_report));
 * tapi_job_factory_destroy(factoryA);
 * @endcode
 *
 * Client with server run
 * -------------------------------------------------
 *
 * @code{.c}
 * rcf_rpc_server *pco_srv = ...;
 * tapi_job_factory_t *factory_srv = NULL;
 *
 * rcf_rpc_server *pco_clnt = ...;
 * tapi_job_factory_t *factory_clnt = NULL;
 *
 * tapi_trex_app *trex_app_srv = NULL;
 * tapi_trex_opt trex_opt_srv = tapi_trex_default_opt;
 * tapi_trex_report trex_report_srv = { 0 };
 *
 * tapi_trex_app *trex_app_clnt = NULL;
 * tapi_trex_opt trex_opt_clnt = tapi_trex_default_opt;
 * tapi_trex_report trex_report_clnt = { 0 };
 *
 * CHECK_RC(tapi_job_factory_rpc_create(pco_srv, &factory_srv));
 * CHECK_RC(tapi_job_factory_rpc_create(pco_clnt, &factory_clnt));
 *
 * trex_opt_srv.servers = TAPI_TREX_SERVERS(
 *  TAPI_TREX_SERVER(
 *      .common.interface = TAPI_TREX_PCI_BY_IFACE(pcoA->ta, "eth0"),
 *      .common.ip = "192.0.0.1",
 *      .common.gw = "192.0.0.2",
 *      .common.ip_range_beg = "192.0.0.1",
 *      .common.ip_range_end = "192.0.0.1",
 *      .common.payload = "HTTP/1.1 200 OK\r\n"
 *              "Content-Type: text/html\r\nConnection: keep-alive\r\n"
 *              "Content-Length: 18\r\n\r\n<html>Hello</html>"
 * ));
 *
 * trex_opt_clnt.clients = TAPI_TREX_CLIENTS(
 *  TAPI_TREX_CLIENT(
 *      .common.interface = TAPI_TREX_PCI_BY_IFACE(pcoB->ta, "eth0"),
 *      .common.ip = "192.0.0.2",
 *      .common.gw = "192.0.0.1",
 *      .common.ip_range_beg = "192.0.0.2",
 *      .common.ip_range_end = "192.0.0.2",
 *      .common.payload = "GET /3384 HTTP/1.1\r\nHo"
 * ));
 *
 * trex_opt_clnt.servers = TAPI_TREX_SERVERS(
 *  TAPI_TREX_SERVER(
 *      .common.ip = "192.0.0.2",
 *      .common.gw = "192.0.0.1",
 *      .common.ip_range_beg = "192.0.0.1",
 *      .common.ip_range_end = "192.0.0.1"
 * ));
 *
 * CHECK_RC(tapi_trex_create(factory_srv, &trex_opt_srv, &trex_app_srv));
 * CHECK_RC(tapi_trex_start(trex_app_srv));
 *
 * CHECK_RC(tapi_trex_create(factory_clnt, &trex_opt_clnt, &trex_app_clnt));
 * CHECK_RC(tapi_trex_start(trex_app_clnt));
 *
 * CHECK_RC(tapi_trex_wait(trex_app_clnt, -1));
 * CHECK_RC(tapi_trex_stop(trex_app_clnt));
 *
 * CHECK_RC(tapi_trex_wait(trex_app_srv, -1));
 * CHECK_RC(tapi_trex_stop(trex_app_srv));
 *
 * // Get and print client report
 * CHECK_RC(tapi_trex_get_report(trex_app_clnt, &trex_report_clnt));
 * CHECK_RC(tapi_trex_report_mi_log(&trex_report_clnt));
 *
 * // Get and print server report
 * CHECK_RC(tapi_trex_get_report(trex_app_srv, &trex_report_srv));
 * CHECK_RC(tapi_trex_report_mi_log(&trex_report_srv));
 *
 * // Destroy TAPI TRex job
 * CHECK_RC(tapi_trex_destroy(pco_srv->ta, trex_app_srv, &trex_opt_srv));
 * CHECK_RC(tapi_trex_destroy_report(&trex_report_srv));
 * tapi_job_factory_destroy(factory_srv);
 *
 * CHECK_RC(tapi_trex_destroy(pco_clnt->ta, trex_app_clnt, &trex_opt_clnt));
 * CHECK_RC(tapi_trex_destroy_report(&trex_report_clnt));
 * tapi_job_factory_destroy(factory_clnt);
 * @endcode
 *
 * @{
 */

/**
 * Create TRex app.
 *
 * @param[in]  factory      Job factory.
 * @param[in]  opt          TRex options.
 * @param[out] app          TRex app handle.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_create(tapi_job_factory_t *factory,
                                 const tapi_trex_opt *opt,
                                 tapi_trex_app **app);

/**
 * Start TRex.
 *
 * @param[in]  app          TRex app handle.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_start(const tapi_trex_app *app);

/**
 * Wait for TRex completion.
 *
 * @param[in]  app          TRex app handle.
 * @param[in]  timeout_ms   Wait timeout in milliseconds.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_wait(const tapi_trex_app *app, int timeout_ms);

/**
 * Stop TRex. It can be started over with tapi_trex_start().
 *
 * @param[in]  app          TRex app handle.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_stop(const tapi_trex_app *app);

/**
 * Send a signal to TRex.
 *
 * @param[in]  app          TRex app handle.
 * @param[in]  signum       Signal to send.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_kill(const tapi_trex_app *app, int signum);

/**
 * Destroy TRex.
 *
 * @param[in]  ta           TRex Test Agent name.
 * @param[in]  app          TRex app handle.
 * @param[in]  opt          TRex options.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_destroy(const char *ta, tapi_trex_app *app,
                                  tapi_trex_opt *opt);

/**
 * Get TRex report.
 *
 * @param[in]  app          TRex app handle.
 * @param[out] report       TRex statistics report.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_get_report(tapi_trex_app *app,
                                     tapi_trex_report *report);

/**
 * Add TRex report to MI logger.
 *
 * @param[in]  report       TRex statistics report.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_report_mi_log(const tapi_trex_report *report);

/**
 * Destroy TRex report to MI logger and freed memory.
 *
 * @param[in]  report       TRex statistics report.
 *
 * @return Status code.
 */
extern te_errno tapi_trex_destroy_report(tapi_trex_report *report);

/**
 * Get all the values of a given parameter from the per port statistics.
 *
 * @param[in]  report           TRex report.
 * @param[in]  param            Type of param.
 * @param[in]  index            Port index.
 * @param[in]  absolute_value   If @c true - return parameter value, otherwise,
 *                              return the differences in the values of each
 *                              pair of consecutive parameters.
 * @param[in]  by_time          If @c true - the parameter value will be divided
 *                              by the time interval between the current and
 *                              previous parameter
 * @param[out] vals             Array of values.
 * @param[out] n_vals           Number of values.
 */
extern void tapi_trex_port_stat_param_series_get(tapi_trex_report *report,
                            tapi_trex_port_stat_enum param, unsigned int index,
                            bool absolute_value, bool by_time,
                            double **vals, unsigned int *n_vals);


/**
 * Get time series from the per port statistics.
 *
 * @param[in]  report       TRex report.
 * @param[out] vals         Array of values.
 * @param[out] n_vals       Number of values.
 */
static inline void
tapi_trex_port_stat_time_series_get(tapi_trex_report *report,
                            double **vals, unsigned int *n_vals)
{
    tapi_trex_port_stat_param_series_get(report,
                            TAPI_TREX_PORT_STAT_CURRENT_TIME, 0, true, false,
                            vals, n_vals);
}

/**
 * Get the value of the port statistics parameter change for each time interval.
 *
 * @param[in]  report       TRex report.
 * @param[in]  param        Type of param.
 * @param[in]  index        Port index.
 * @param[out] vals         Array of values.
 * @param[out] n_vals       Number of values.
 */
static inline void
tapi_trex_port_stat_param_series_by_time_get(tapi_trex_report *report,
                            tapi_trex_port_stat_enum param, unsigned int index,
                            double **vals, unsigned int *n_vals)
{
    tapi_trex_port_stat_param_series_get(report,
                            param, index, false, true, vals, n_vals);
}

/**
 * Get the statisctical data for a given parameter from the per-port statistics.
 *
 * @param[in]  report       TRex report.
 * @param[in]  param        Type of param.
 * @param[in]  index        Port index.
 * @param[in]  time_start   Use values starting from the specified time
 *                          (in seconds).
 * @param[in]  time_end     Use values up to the specified time (in seconds).
 * @param[out] min          Minimal value (may be @c NULL).
 * @param[out] avg          Average value (may be @c NULL).
 * @param[out] median       Median value (may be @c NULL).
 * @param[out] max          Maximum value (may be @c NULL).
 *
 * @return Status code.
 * @retval TE_ENODATA       Per-port statistics do not contain data.
 * @retval TE_ERANGE        The @p time_start is too long, or the @p time_end
 *                          is too short in the interface statistics.
 * @retval @c 0             The result is successful.
 */
extern te_errno tapi_trex_port_stat_data_get(tapi_trex_report *report,
                            tapi_trex_port_stat_enum param, unsigned int index,
                            double time_start, double time_end, double *min,
                            double *avg, double *median, double *max);

/**
 * Get the value of the optional TRex filter for the client side.
 *
 * @param[in]  report   TRex report.
 * @param[in]  name     Filter name.
 * @param[out] value    Filter value.
 *
 * @return Status code.
 * @retval TE_EINVAL    There is no filter with that name.
 * @retval @c 0         The result is successful.
 */
extern te_errno tapi_trex_opt_flt_cl_get(tapi_trex_report *report,
                                         const char *name, uint64_t *value);

/**
 * Get the value of the optional TRex filter for the server side.
 *
 * @param[in]  app      TRex app handle.
 * @param[in]  name     Filter name.
 * @param[out] value    Filter value.
 *
 * @return Status code.
 * @retval TE_EINVAL    There is no filter with that name.
 * @retval @c 0         The result is successful.
 */
extern te_errno tapi_trex_opt_flt_srv_get(tapi_trex_report *report,
                                          const char *name, uint64_t *value);

/**@}*/

#ifdef __cplusplus
} /* extern "C" */
#endif
#endif /* !__TE_TAPI_TREX_H__ */
/**@} <!-- END tapi_trex --> */
