/* SPDX-License-Identifier: Apache-2.0 */
/** @file
 * @brief Tester Subsystem
 *
 * Requirements definitions.
 *
 *
 * Copyright (C) 2004-2022 OKTET Labs Ltd. All rights reserved.
 */

#ifndef __TE_TESTER_REQS_H__
#define __TE_TESTER_REQS_H__

#include "te_defs.h"
#include "te_queue.h"
#include "te_errno.h"
#include "logic_expr.h"
#include "tester_flags.h"

#ifdef __cplusplus
extern "C" {
#endif


/** Element of the list of requirements */
typedef struct test_requirement {
    TAILQ_ENTRY(test_requirement)   links;  /**< List links */
    char       *id;         /**< Identifier */
    char       *ref;        /**< Reference */
    bool sticky;     /**< Is it sticky requirement? */
} test_requirement;

/** Head of the list of requirements */
typedef TAILQ_HEAD(test_requirements, test_requirement) test_requirements;


/* Forwards */
struct tester_ctx;
struct run_item;
struct test_iter_arg;


/**
 * Create a new target requirement and insert it using logical 'and'
 * with current target.
 *
 * @param targets   Location of the target requirements expression
 * @param req       String requirement
 *
 * @return Status code.
 * @retval 0            Success.
 * @retval TE_ENOMEM    Memory allocation failure.
 */
extern te_errno tester_new_target_reqs(logic_expr **targets,
                                       const char  *req);


/**
 * Clone list of requirements.
 *
 * @param reqs      List of requirements to be cloned
 * @param new_reqs  New list of requirements (must be initialized)
 */
extern void test_requirements_clone(const test_requirements *reqs,
                                    test_requirements *new_reqs);

/**
 * Free list of requirements.
 *
 * @param reqs      List of requirements to be freed
 */
extern void test_requirements_free(test_requirements *reqs);

/**
 * Determine whether running of the test required.
 *
 * @param targets       Target requirements expression
 * @param sticky_reqs   List of collected sticky requirements
 * @param test          Test to be checked
 * @param args          Array with test iteration arguments (run item
 *                      has fixed number of arguments)
 * @param flags         Current Tester context flags
 * @param quiet         Be quiet
 *
 * @retval @c true      Run is required
 * @retval @c false     Run is not required
 */
extern bool tester_is_run_required(
                   const logic_expr           *targets,
                   const test_requirements    *sticky_reqs,
                   const struct run_item      *test,
                   const struct test_iter_arg *args,
                   tester_flags                flags,
                   bool quiet);

/**
 * Add sticky requirements to the context.
 *
 * @param sticky_reqs   List of requirements in the current context
 * @param reqs          List of requirements
 *
 * @return Status code (always returns @c 0).
 */
extern te_errno tester_get_sticky_reqs(test_requirements *sticky_reqs,
                                       const test_requirements *reqs);

/**
 * Get pointer to requirements for a run item.
 *
 * @param ri      Run item.
 *
 * @return Pointer to associated requirements.
 */
const test_requirements *tester_get_ri_reqs(const struct run_item *ri);

/**
 * Get requirement identifier in specified context of parameters.
 *
 * @param req           A requirement.
 * @param n_args        Number of arguments.
 * @param args          Test iteration arguments.
 *
 * @return Requirement Id.
 */
extern const char *test_req_id(const test_requirement *req,
                               unsigned int n_args,
                               const struct test_iter_arg *args);

/**
 * Print requirements expression to static buffer.
 *
 * @param expr      Requirements expression
 *
 * @return Pointer to the static buffer with printed expression.
 */
extern const char *tester_reqs_expr_to_string(const logic_expr *expr);

#ifdef __cplusplus
} /* extern "C" */
#endif
#endif /* !__TE_TESTER_REQS_H__ */
