/* SPDX-License-Identifier: Apache-2.0 */
/** @file
 * @brief Test API to work with the files on the engine and TA.
 *
 * @defgroup ts_tapi_file Engine and TA files management
 * @ingroup te_ts_tapi
 * @{
 *
 * Functions for convinient work with the files on the engine and TA.
 *
 *
 * Copyright (C) 2004-2022 OKTET Labs Ltd. All rights reserved.
 */

#ifndef __TE_TAPI_FILE_H__
#define __TE_TAPI_FILE_H__

#include "te_defs.h"
#include "te_string.h"
#include "te_expand.h"
#include "tapi_cfg_base.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Generate a unique basename for a file.
 *
 * If @p dest is @c NULL, a fresh string is allocated and returned.
 *
 * @param[out] dest  The string to hold the name or @c NULL.
 *
 * @note The name is appended to the string contents.
 *       That way it is easier to construct derived pathnames
 *       and similar stuff.
 *
 * @return the pointer to the contents of @p dest or a heap-allocated buffer
 */
extern char *tapi_file_make_name(te_string *dest);

/**
 * Generate a unique pathname for a file on the Engine side.
 *
 * If @p dest is @c NULL, a fresh string is allocated and returned.
 *
 * @param[out] dest    The string to hold the name or @c NULL.
 * @param[in]  dirname Directory component (may be @c NULL,
 *                     in which case a relative name is generated)
 * @param[in]  suffix  A custom suffix to add to a generated
 *                     pathname (may be @c NULL).
 *
 * @note The name is appended to the string contents.
 *
 * @return the pointer to the contents of @p dest or a heap-allocated buffer
 */
extern char *tapi_file_make_custom_pathname(te_string *dest,
                                            const char *dirname,
                                            const char *suffix);

/**
 * Generate a unique pathname for a file on the Engine side.
 *
 * If @p dest is @c NULL, a fresh string is allocated and returned.
 *
 * @param[out] dest  The string to hold the name or @c NULL.
 *
 * @note The name is appended to the string contents.
 * @note @c TE_TMP env variable must be set.
 *
 * @return the pointer to the contents of @p dest or a heap-allocated buffer
 */
extern char *tapi_file_make_pathname(te_string *dest);


/**
 * Construct a pathname from parts.
 *
 * If @p path is not @c NULL, uses te_file_join_filename()
 * to construct a complete filename.
 * Otherwise, it behaves like tapi_file_make_custom_pathname(),
 * generating a unique filename under @p dirname.
 *
 * If @p path is not @c NULL, it may be either a relative or
 * an absolute pathname. In the latter case @p dirname is ignored.
 *
 * If @p dest is @c NULL, a fresh string is allocated and returned.
 *
 * @param[out] dest      The string to hold the name or @c NULL.
 * @param[in]  dirname   Directory name (may be @c NULL)
 * @param[in]  path      Pathname (absolute, relative or @c NULL)
 * @param[in]  suffix    A suffix to append to a pathname
 *                       (may be @c NULL).
 *
 * @note The name is appended to the string contents.
 *
 * @return the pointer to the contents of @p dest or a heap-allocated buffer
 */
extern char *tapi_file_join_pathname(te_string *dest,
                                     const char *dirname,
                                     const char *path,
                                     const char *suffix);


/**
 * Resolve a pathname relative to one of the agent directories.
 *
 * te_file_join_filename() is used for resolving, so pathname
 * components need not exist and symlinks are not resolved.
 *
 * If @p dest is @c NULL, a fresh string is allocated and returned.
 *
 * @param[out] dest      The string to hold the name or @c NULL.
 * @param[in]  ta        Agent name.
 * @param[in]  base_dir  Agent base directory.
 * @param[in]  relname   Relative filename.
 *
 * @note The name is appended to the string contents.
 *
 * @return the pointer to the contents of @p dest or a heap-allocated buffer
 *
 * @sa tapi_cfg_base_get_ta_dir()
 */
extern char *tapi_file_resolve_ta_pathname(te_string *dest,
                                           const char *ta,
                                           tapi_cfg_base_ta_dir base_dir,
                                           const char *relname);

/**
 * Generate unique basename for file.
 *
 * @return generated name
 *
 * @deprecated
 * The function returns a pointer to
 * a static buffer, so it is inherently unreliable.
 * Use tapi_file_make_name() instead.
 */
extern char *tapi_file_generate_name(void) TE_DEPRECATED;

/**
 * Generate unique pathname for file on the engine.
 *
 * @return generated name
 *
 * @deprecated
 * The function returns a pointer to
 * a static buffer, so it is inherently unreliable.
 * Use tapi_file_make_pathname() instead.
 */
extern char *tapi_file_generate_pathname(void) TE_DEPRECATED;

/**
 * Create file in the TE temporary directory.
 *
 * @param len   file length
 * @param c     file content pattern
 *
 * @return name (memory is allocated) of the file or
 *         @c NULL in the case of failure
 */
extern char *tapi_file_create_pattern(size_t len, char c);

/**
 * Create file in the TE temporary directory with the specified content.
 *
 * @param len     file length
 * @param buf     buffer with the file content
 * @param random  if @c true, fill buffer with random data
 *
 * @return name (memory is allocated) of the file or
 *         @c NULL in the case of failure
 */
extern char *tapi_file_create(size_t len, char *buf, bool random);

/**
 * Create file in the specified directory on the TA.
 *
 * @param ta            Test Agent name
 * @param filename      pathname of the file
 * @param fmt           format string for the file content
 *
 * @return Status code
 */
extern te_errno tapi_file_create_ta(const char *ta, const char *filename,
                                    const char *fmt, ...)
    TE_LIKE_PRINTF(3, 4);

/**
 * Create local file, copy it to TA, remove local file.
 * The function does the same thing as tapi_file_create_ta(),
 * but it creates local file with specified name instead of
 * using automatically generated name.
 *
 * @param ta            Test Agent name
 * @param lfile         pathname of the local file
 * @param rfile         pathname of the file on TA
 * @param fmt           format string for the file content
 *
 * @return Status code
 */
extern te_errno tapi_file_create_ta_r(const char *ta,
                                      const char *lfile,
                                      const char *rfile,
                                      const char *fmt, ...)
    TE_LIKE_PRINTF(4, 5);;

/**
 * Read file content from the TA.
 *
 * @param ta            Test Agent name
 * @param filename      pathname of the file
 * @param pbuf          location for buffer allocated by the routine
 *
 * @return Status code
 */
extern te_errno tapi_file_read_ta(const char *ta, const char *filename,
                                  char **pbuf);


/**
 * Like tapi_file_create_ta(), but it appends data to the file.
 *
 * If the file does not exist, it is created.
 *
 * @param ta            Test Agent name
 * @param filename      pathname of the file
 * @param fmt           format string for the file content
 *
 * @return Status code
 */
extern te_errno tapi_file_append_ta(const char *ta, const char *filename,
                                    const char *fmt, ...)
    TE_LIKE_PRINTF(3, 4);

/**
 * The kind of a chunk in #tapi_file_chunk_spec.
 */
typedef enum tapi_file_chunk_spec_kind {
    /** The last chunk in the list. */
    TAPI_FILE_CHUNK_SPEC_KIND_END,
    /**
     * The literal chunk: @a spec is treated
     * as a literal sequence of characters.
     *
     * If @a maxlen is not zero, it is treated
     * as the size of the string, otherwise @a spec
     * must be zero-terminated.
     *
     * @a minlen may be
     * used to specify the length of the chunk
     * (see @p fitlen of te_file_write_string()
     * for the exact semantics).
     */
    TAPI_FILE_CHUNK_SPEC_KIND_LITERAL,
    /**
     * The simple pattern chunk: @a spec is
     * treated as a block pattern as in
     * te_compile_buf_pattern().
     *
     * @a minlen and @a maxlen are used to
     * determine the length of the generated
     * block as in te_make_spec_buf().
     */
    TAPI_FILE_CHUNK_SPEC_KIND_PATTERN,
    /**
     * The compound chunk: @a nested is a list
     * of sub-chunks terminated by a
     * #TAPI_FILE_CHUNK_SPEC_KIND_END.
     *
     * @a minlen and @a maxlen are used to
     * determine the number of times the list
     * of sub-chunks is reused.
     */
    TAPI_FILE_CHUNK_SPEC_KIND_COMPOUND,
} tapi_file_chunk_spec_kind;

/**
 * A description of a chunk for tapi_file_create_by_spec_ta().
 *
 * When a list of #tapi_file_chunk_spec is passed to
 * tapi_file_create_by_spec_ta(), the last item must have
 * @a kind set to #TAPI_FILE_CHUNK_SPEC_KIND_END.
 */
typedef struct tapi_file_chunk_spec {
    /** The kind of the chunk. */
    tapi_file_chunk_spec_kind kind;
    /** Minimum length of a generated chunk. */
    size_t minlen;
    /** Maximum length of a generated chunk. */
    size_t maxlen;
    union {
        /**
         * The chunk specification, either a literal string or
         * a pattern as in te_compile_buf_pattern().
         */
        const char *spec;
        /**
         * The list of sub-chunks, must be terminated by
         * #TAPI_FILE_CHUNK_SPEC_KIND_END.
         */
        const struct tapi_file_chunk_spec *nested;
    } u;
} tapi_file_chunk_spec;

/**
 * Create the file on the TA according to a list of content patterns.
 *
 * @note Currently the content is generated locally and then
 *       transferred to the agent, so the function may not work very well
 *       with large file sizes.
 *
 * @param  ta           Test Agent name (may be @c NULL, in which case
 *                      the file is created on the Engine side).
 * @param  filename     Pathname of the file at the agent.
 * @param  specs        List of chunk specifications
 *                      (the last item should have @a kind field
 *                      set to #TAPI_FILE_CHUNK_SPEC_KIND_END.
 *
 * @return Status code.
 */
extern te_errno tapi_file_create_by_spec_ta(const char *ta,
                                            const char *filename,
                                            const tapi_file_chunk_spec *specs);

/**
 * Copy file from the one TA to other or between the Engine and an agent.
 *
 * @param ta_src        source Test Agent
 *                      (@c NULL if the source is the Engine)
 * @param src           source file name
 * @param ta_dst        destination Test Agent
 *                      (@c NULL if the source is the Engine)
 * @param dst           destination file name
 *
 * @return Status code
 *
 * @todo Currently the function does not support copying files on the Engine
 *       locally, so both @p ta_src and @p ta_dst cannot be @c NULL at the
 *       same time.
 */
extern te_errno tapi_file_copy_ta(const char *ta_src, const char *src,
                                  const char *ta_dst, const char *dst);


/**
 * Generate a file by expanding references in @p template.
 *
 * The expansion is done with te_string_expand_kvpairs() using
 * @p posargs for positional argument references and @p kvpairs for
 * named variable references.
 *
 * If @p ta is not @c NULL, the file is copied to a given agent; otherwise
 * it is created locally on the Engine host.
 *
 * @param ta            Test Agent name
 *                      (may be @c NULL, then Engine is assumed)
 * @param template      file content template
 * @param posargs       array of positional arguments (may be @c NULL)
 * @param kvpairs       kvpairs of named variables
 * @param filename_fmt  format string of a generated pathname
 * @param ...           arguments
 *
 * @return status code
 */
extern te_errno tapi_file_expand_kvpairs(const char *ta,
                                         const char *template,
                                         const char *posargs
                                         [TE_EXPAND_MAX_POS_ARGS],
                                         const te_kvpair_h *kvpairs,
                                         const char *filename_fmt, ...);

/**
 * Unlink file on the TA.
 *
 * @param ta            Test Agent name
 * @param path_fmt      Format string to make path to be deleted
 *
 * @return Status code.
 */
extern te_errno tapi_file_ta_unlink_fmt(const char *ta,
                                        const char *path_fmt, ...)
    TE_LIKE_PRINTF(2, 3);

#ifdef __cplusplus
} /* extern "C" */
#endif
#endif /* !__TE_TAPI_FILE_H__ */

/**@} <!-- END ts_tapi_file --> */
