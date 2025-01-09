/* SPDX-License-Identifier: Apache-2.0 */
/* Copyright (C) 2023 OKTET Labs Ltd. All rights reserved. */
/** @file
 * @brief Unbound DNS server config file generator tool TAPI.
 *
 * TAPI to handle unbound DNS server config file generator tool.
 */

#define TE_LGR_USER "TAPI UNBOUND CFG"

#include "tapi_dns_common.h"
#include "tapi_dns_unbound.h"
#include "tapi_job_opt.h"
#include "te_alloc.h"
#include "te_str.h"
#include "te_sockaddr.h"
#include "te_enum.h"
#include "tapi_rpc_unistd.h"
#include "tapi_file.h"
#include "tapi_cfg_base.h"

#define INDENT "    "

const tapi_dns_unbound_cfg_opt tapi_dns_unbound_cfg_default_opt = {
    .verbosity = TAPI_DNS_UNBOUND_VERBOSE,
    .includes.n = 0,
    .includes.filename = NULL,
    .username = NULL,
    .chroot = NULL,
    .directory = NULL,
    .interfaces.n = 0,
    .interfaces.addr = NULL,
    .outgoing_interfaces.n = 0,
    .outgoing_interfaces.addr = NULL,
    .access_controls.n = 0,
    .access_controls.rule = NULL,
    .private_addresses.n = 0,
    .private_addresses.addr = NULL,
    .private_domain = NULL,
    .port = TAPI_JOB_OPT_UINT_UNDEF,
    .so_reuseport = true,
    .auth_zones.n = 0,
    .auth_zones.zone = NULL,
    .num_threads = TAPI_JOB_OPT_UINT_UNDEF,
    .num_queries_per_thread = TAPI_JOB_OPT_UINT_UNDEF,
    .jostle_timeout = TAPI_JOB_OPT_UINT_UNDEF,
    .minimal_responses = true,
    .do_ip4 = true,
    .do_ip6 = true,
    .do_udp = true,
    .do_tcp = true,
    .incoming_num_tcp = TAPI_JOB_OPT_UINT_UNDEF,
    .outgoing_num_tcp = TAPI_JOB_OPT_UINT_UNDEF,
    .cache_max_ttl = TAPI_JOB_OPT_UINT_UNDEF,
    .cache_min_ttl = TAPI_JOB_OPT_UINT_UNDEF,
    .so_rcvbuf = TAPI_JOB_OPT_UINT_UNDEF,
    .so_sndbuf = TAPI_JOB_OPT_UINT_UNDEF,
};

static const te_enum_map tapi_dns_unbound_cfg_verbose_mapping[] = {
    {.name = "0", .value = TAPI_DNS_UNBOUND_NOT_VERBOSE},
    {.name = "1", .value = TAPI_DNS_UNBOUND_VERBOSE},
    {.name = "2", .value = TAPI_DNS_UNBOUND_MORE_VERBOSE},
    {.name = "3", .value = TAPI_DNS_UNBOUND_VERBOSE_LL_QUERY},
    {.name = "4", .value = TAPI_DNS_UNBOUND_VERBOSE_LL_ALGO},
    {.name = "5", .value = TAPI_DNS_UNBOUND_VERBOSE_LL_CACHE},
    TE_ENUM_MAP_END
};

static const te_enum_map tapi_dns_unbound_cfg_ac_action_mapping[] = {
    {.name = "deny", .value = TAPI_DNS_UNBOUND_CFG_AC_DENY},
    {.name = "refuse", .value = TAPI_DNS_UNBOUND_CFG_AC_REFUSE},
    {.name = "allow", .value = TAPI_DNS_UNBOUND_CFG_AC_ALLOW},
    {.name = "allow_setrd", .value = TAPI_DNS_UNBOUND_CFG_AC_ALLOW_SETRD},
    {.name = "allow_snoop", .value = TAPI_DNS_UNBOUND_CFG_AC_ALLOW_SNOOP},
    {.name = "deny_non_local", .value = TAPI_DNS_UNBOUND_CFG_AC_DENY_NON_LOCAL},
    {.name = "refuse_non_local",
     .value = TAPI_DNS_UNBOUND_CFG_AC_REFUSE_NON_LOCAL},
    TE_ENUM_MAP_END
};

static const te_enum_map tapi_dns_unbound_cfg_bool_mapping[] = {
    {.name = "yes", .value = true},
    {.name = "no",  .value = false},
    TE_ENUM_MAP_END
};

static const tapi_job_opt_bind unbound_cfg_server_binds[] = TAPI_JOB_OPT_SET(
    TAPI_JOB_OPT_DUMMY("use-syslog: no"),

    TAPI_JOB_OPT_QUOTED_STRING("username: ", "\"",
                               tapi_dns_unbound_cfg_opt, username),
    TAPI_JOB_OPT_QUOTED_STRING("chroot: ", "\"",
                               tapi_dns_unbound_cfg_opt, chroot),
    TAPI_JOB_OPT_QUOTED_STRING("directory: ", "\"",
                               tapi_dns_unbound_cfg_opt, directory),
    TAPI_JOB_OPT_ENUM("verbosity: ", true, tapi_dns_unbound_cfg_opt, verbosity,
                      tapi_dns_unbound_cfg_verbose_mapping),

    TAPI_JOB_OPT_UINT_T("port: ", true, NULL, tapi_dns_unbound_cfg_opt, port),
    TAPI_JOB_OPT_ENUM_BOOL("so-reuseport: ", true, tapi_dns_unbound_cfg_opt,
                           so_reuseport, tapi_dns_unbound_cfg_bool_mapping),

    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_opt,
        interfaces.n, interfaces.addr,
        TAPI_JOB_OPT_STRUCT("interface: ", true, "@", NULL,
			    TAPI_JOB_OPT_STRING(NULL, false,
						tapi_dns_unbound_cfg_address, addr),
			    TAPI_JOB_OPT_UINT_T(NULL, false, NULL,
						tapi_dns_unbound_cfg_address, port))),

    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_opt,
        outgoing_interfaces.n, outgoing_interfaces.addr,
        TAPI_JOB_OPT_CONTENT(TAPI_JOB_OPT_SOCKADDR_PTR,
                             "outgoing-interface: ", true)),

    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_opt,
        access_controls.n, access_controls.rule,
        TAPI_JOB_OPT_STRUCT("access-control: ", true, " ", NULL,
			    TAPI_JOB_OPT_SOCKADDR_SUBNET(NULL, false,
							 tapi_dns_unbound_cfg_ac, subnet),
			    TAPI_JOB_OPT_ENUM(NULL, false,
					      tapi_dns_unbound_cfg_ac, action,
					      tapi_dns_unbound_cfg_ac_action_mapping))),

    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_opt,
        private_addresses.n, private_addresses.addr,
        TAPI_JOB_OPT_CONTENT(TAPI_JOB_OPT_SOCKADDR_SUBNET,
                             "private-address: ", true)),

    TAPI_JOB_OPT_STRING("private-domain: ", true, tapi_dns_unbound_cfg_opt,
                        private_domain),

    TAPI_JOB_OPT_UINT_T("num-threads: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, num_threads),
    TAPI_JOB_OPT_UINT_T("num-queries-per-thread: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, num_queries_per_thread),
    TAPI_JOB_OPT_UINT_T("jostle-timeout: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, jostle_timeout),
    TAPI_JOB_OPT_ENUM_BOOL("minimal-responses: ", true,
                           tapi_dns_unbound_cfg_opt, minimal_responses,
                           tapi_dns_unbound_cfg_bool_mapping),

    TAPI_JOB_OPT_ENUM_BOOL("do-ip4: ", true,
                           tapi_dns_unbound_cfg_opt, do_ip4,
                           tapi_dns_unbound_cfg_bool_mapping),
    TAPI_JOB_OPT_ENUM_BOOL("do-ip6: ", true,
                           tapi_dns_unbound_cfg_opt, do_ip6,
                           tapi_dns_unbound_cfg_bool_mapping),
    TAPI_JOB_OPT_ENUM_BOOL("do-udp: ", true,
                           tapi_dns_unbound_cfg_opt, do_udp,
                           tapi_dns_unbound_cfg_bool_mapping),
    TAPI_JOB_OPT_ENUM_BOOL("do-tcp: ", true,
                           tapi_dns_unbound_cfg_opt, do_tcp,
                           tapi_dns_unbound_cfg_bool_mapping),

    TAPI_JOB_OPT_UINT_T("incoming-num-tcp: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, incoming_num_tcp),
    TAPI_JOB_OPT_UINT_T("outgoing-num-tcp: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, outgoing_num_tcp),

    TAPI_JOB_OPT_UINT_T("cache-max-ttl: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, cache_max_ttl),
    TAPI_JOB_OPT_UINT_T("cache-min-ttl: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, cache_min_ttl),

    TAPI_JOB_OPT_UINT_T("so-rcvbuf: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, so_rcvbuf),
    TAPI_JOB_OPT_UINT_T("so-sndbuf: ", true, NULL,
                        tapi_dns_unbound_cfg_opt, so_sndbuf),

    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_opt,
        includes.n, includes.filename,
        TAPI_JOB_OPT_CONTENT(TAPI_JOB_OPT_QUOTED_STRING,
                             "include: ", "\""))
);

static const tapi_job_opt_bind unbound_cfg_auth_zone_binds[] = TAPI_JOB_OPT_SET(
    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_opt,
        auth_zones.n, auth_zones.zone,
        TAPI_JOB_OPT_STRUCT("auth-zone:\n" INDENT, true, "\n" INDENT, NULL,
			    TAPI_JOB_OPT_STRING("name: ", true,
						tapi_dns_unbound_cfg_auth_zone, name),
			    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_auth_zone,
						   primaries.n, primaries.addr,
						   TAPI_JOB_OPT_STRUCT("primary: ", true, "@", NULL,
								       TAPI_JOB_OPT_STRING(NULL, false,
											   tapi_dns_unbound_cfg_address, addr),
								       TAPI_JOB_OPT_UINT_T(NULL, false, NULL,
											   tapi_dns_unbound_cfg_address, port))),
			    TAPI_JOB_OPT_ARRAY_PTR(tapi_dns_unbound_cfg_auth_zone,
						   primary_urls.n, primary_urls.url,
						   TAPI_JOB_OPT_CONTENT(TAPI_JOB_OPT_STRING, "url: ", true)),
			    TAPI_JOB_OPT_STRING("zonefile: ", true,
						tapi_dns_unbound_cfg_auth_zone, zonefile)))
);

static const tapi_job_opt_bind unbound_cfg_remote_control_binds[] =
    TAPI_JOB_OPT_SET(
        TAPI_JOB_OPT_DUMMY("control-enable: no"),
        TAPI_JOB_OPT_DUMMY("control-use-cert: no")
    );

static void
build_cfg_group(const char *prefix,
                const tapi_dns_unbound_cfg_opt *opt,
                const tapi_job_opt_bind *binds,
                const char *sep,
                te_string *res)
{
    te_vec args = TE_VEC_INIT(char *);

    tapi_job_opt_build_args(prefix, binds, opt, &args);
    te_string_join_vec(res, &args, sep);
    te_string_append(res, "\n");

    te_vec_deep_free(&args);
}

te_errno
tapi_dns_unbound_cfg_create(const char *ta,
                            const tapi_dns_unbound_cfg_opt *opt,
                            const char *base_dir,
                            const char *filename,
                            char **result_pathname)
{
    te_string cfg_data = TE_STRING_INIT;
    char *res_path = NULL;
    te_errno rc;

    if (opt == NULL)
        opt = &tapi_dns_unbound_cfg_default_opt;

    build_cfg_group("server:", opt, unbound_cfg_server_binds,
                    "\n" INDENT, &cfg_data);
    build_cfg_group("remote-control:", opt, unbound_cfg_remote_control_binds,
                    "\n" INDENT, &cfg_data);
    build_cfg_group("", opt, unbound_cfg_auth_zone_binds, "\n", &cfg_data);

    res_path = tapi_dns_gen_filepath(ta, base_dir, filename);
    rc = tapi_file_create_ta(ta, res_path, "%s", cfg_data.ptr);
    te_string_free(&cfg_data);
    if (rc != 0)
    {
        free(res_path);
        ERROR("Failed to create config file");
        return rc;
    }

    if (result_pathname != NULL)
        *result_pathname = res_path;
    else
        free(res_path);

    return 0;
}

void
tapi_dns_unbound_cfg_destroy(const char *ta, const char *cfg_file)
{
    if (cfg_file != NULL)
        tapi_file_ta_unlink_fmt(ta, "%s", cfg_file);
}
