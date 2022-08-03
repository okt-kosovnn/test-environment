/* SPDX-License-Identifier: Apache-2.0 */
/** @file
 * @brief YAML configuration file processing facility
 *
 * API definitions.
 *
 * Copyright (C) 2018-2022 OKTET Labs Ltd. All rights reserved.
 */

#ifndef __TE_CONF_YAML_H__
#define __TE_CONF_YAML_H__

#include "te_errno.h"

/**
 * Parse YAML configuration file.
 *
 * The input file must be a YAML document containing dynamic history
 * statements. One may leverage these statements to create instances
 * for the objects maintained by the primary configuration file. The
 * instances may come with logical expressions either per individual
 * entry or per a bunch of entries to indicate conditions which must
 * be true for the instances to hit the XML document being generated.
 *
 * The XML document will be consumed directly by cfg_dh_process_file().
 *
 * @param filename          The input file path
 * @param expand_vars       List of key-value pairs for expansion in file,
 *                          @c NULL if environment variables are used for
 *                          substitutions
 * @param xn_history_root   XML node containing translated yaml file content,
 *                          @c NULL if yaml file is not being included
 * @param conf_dirs         Directories where additionally Configurator should
 *                          search files via include directive
 *                          @c NULL if there are no configuration directories.
 *
 * @return Status code.
 */
extern te_errno parse_config_yaml(const char *filename,
                                  te_kvpair_h *expand_vars,
                                  xmlNodePtr xn_history_root,
                                  const char *conf_dirs);

/**
 * Parse YAML backup file to XML structure
 *
 * @param file         path name of the file
 * @param root         XML structure, it should be freed
 *
 * @return int status code (see te_errno.h)
 */
te_errno
yaml_parse_backup_to_xml(const char *filename, xmlNodePtr ptr_backup);

/**
 * Modify YAML backup file using filters and write it to target_backup file
 *
 * @param filter_filename       path name of the filter file
 * @param current_backup        path name of the current backup file
 * @param target_backup         path name of the target backup file
 *
 * @return int status code (see te_errno.h)
 */
te_errno
yaml_parse_filter_subtrees(const te_vec *subtrees, const char *current_backup,
                           const char *target_backup);

#endif /* __TE_CONF_YAML_H__ */
