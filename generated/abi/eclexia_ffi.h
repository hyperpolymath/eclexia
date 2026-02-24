/**
 * Eclexia Resource System — C ABI Header (Auto-generated)
 *
 * Bidirectional FFI for Eclexia's resource tracking, shadow prices,
 * adaptive function dispatch, and fault isolation.
 *
 * OUTBOUND: Eclexia programs call into optimised native implementations
 * INBOUND:  External code (C, Rust, Python ctypes, etc.) calls into Eclexia runtime
 *
 * Generated from: src/abi/ResourceABI.idr
 * Implemented in:  ffi/zig/src/resource.zig
 *
 * SPDX-License-Identifier: PMPL-1.0-or-later
 * SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
 */

#ifndef ECLEXIA_FFI_H
#define ECLEXIA_FFI_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ========================================================================== */
/* Result Codes                                                                */
/* ========================================================================== */

typedef enum {
    ECL_OK              = 0,
    ECL_ERROR           = 1,
    ECL_INVALID_PARAM   = 2,
    ECL_OUT_OF_MEMORY   = 3,
    ECL_NULL_POINTER    = 4,
    ECL_BUDGET_EXCEEDED = 5,
    ECL_FUSE_OPEN       = 6,
    ECL_SLA_VIOLATED    = 7,
} ecl_result_t;

/* ========================================================================== */
/* Resource Dimensions                                                         */
/* ========================================================================== */

typedef enum {
    ECL_DIM_ENERGY  = 1,
    ECL_DIM_TIME    = 2,
    ECL_DIM_MEMORY  = 3,
    ECL_DIM_CARBON  = 4,
    ECL_DIM_POWER   = 5,
} ecl_dimension_t;

/* ========================================================================== */
/* Strategy Selection                                                          */
/* ========================================================================== */

typedef enum {
    ECL_STRATEGY_FAST      = 0,
    ECL_STRATEGY_BALANCED  = 1,
    ECL_STRATEGY_EFFICIENT = 2,
    ECL_STRATEGY_PRECISE   = 3,
} ecl_strategy_t;

/* ========================================================================== */
/* Fuse States                                                                 */
/* ========================================================================== */

typedef enum {
    ECL_FUSE_CLOSED    = 0,
    ECL_FUSE_OPEN      = 1,
    ECL_FUSE_HALF_OPEN = 2,
} ecl_fuse_state_t;

/* ========================================================================== */
/* Core Structs (cache-line aware)                                             */
/* ========================================================================== */

/** Resource value with dimensional tag (16 bytes) */
typedef struct {
    double   amount;
    uint32_t dimension;
    uint32_t _padding;
} ecl_resource_t;

/** Shadow price observation (24 bytes) */
typedef struct {
    double   price;
    uint32_t dimension;
    uint32_t _padding;
    uint64_t timestamp;
} ecl_shadow_price_t;

/** Resource budget tracker (32 bytes) */
typedef struct {
    double   total;
    double   consumed;
    double   remaining;
    uint32_t dimension;
    uint32_t _padding;
} ecl_budget_t;

/** Adaptive selection context (64 bytes, cache-line aligned) */
typedef struct __attribute__((aligned(64))) {
    double energy_remaining;
    double time_remaining;
    double memory_remaining;
    double carbon_remaining;
    double shadow_energy;
    double shadow_time;
    double shadow_memory;
    double shadow_carbon;
} ecl_selection_ctx_t;

/** Fuse configuration */
typedef struct {
    double   trip_threshold;
    uint64_t reset_timeout_ns;
    uint32_t half_open_quota;
    uint32_t dimension;
} ecl_fuse_config_t;

/* ========================================================================== */
/* OUTBOUND: Eclexia -> Native                                                 */
/* ========================================================================== */

/** Observe shadow price for a resource dimension (lock-free) */
double ecl_shadow_price_observe(uint32_t dimension);

/** Update shadow price (lock-free, notifies subscribers) */
uint32_t ecl_shadow_price_update(uint32_t dimension, double new_price);

/** Consume resources (atomic CAS on budget) */
uint32_t ecl_resource_consume(uint32_t dimension, double amount);

/** Select optimal strategy (SIMD-accelerated) */
uint32_t ecl_adaptive_select(const ecl_selection_ctx_t *ctx);

/** Compute Pareto frontier (SIMD dominance checking) */
uint32_t ecl_pareto_compute(const double *points, uint32_t num_points,
                            uint32_t num_objectives);

/** Check SLA constraint */
uint32_t ecl_sla_check(const void *sla, const ecl_budget_t *budget);

/** Check fuse state */
uint32_t ecl_fuse_check(const ecl_fuse_config_t *fuse);

/** Propagate budget (zero-copy) */
uint32_t ecl_budget_propagate(const ecl_budget_t *parent,
                              ecl_budget_t *child, double fraction);

/* ========================================================================== */
/* INBOUND: Native -> Eclexia                                                  */
/* ========================================================================== */

/** Create resource tracker (returns handle) */
uint64_t ecl_tracker_create(uint32_t dimension, double total_budget);

/** Get remaining budget */
double ecl_tracker_remaining(uint64_t tracker_handle);

/** Register external resource provider */
uint32_t ecl_register_provider(uint32_t dimension, uint64_t callback_ptr);

/** Subscribe to shadow price updates */
typedef void (*ecl_shadow_callback_t)(uint32_t dimension, double price);
uint32_t ecl_shadow_subscribe(uint32_t dimension, ecl_shadow_callback_t callback);

/** Inject external measurement (hardware monitor, carbon API, etc.) */
uint32_t ecl_inject_measurement(uint32_t dimension, double value,
                                uint64_t timestamp_ns);

/* ========================================================================== */
/* Batch Operations (SIMD-optimised)                                           */
/* ========================================================================== */

/** Observe all shadow prices at once */
uint32_t ecl_shadow_price_observe_all(double *out_prices);

/** Check all budgets (returns bitmask of exceeded dimensions) */
uint32_t ecl_budget_check_all(double threshold);

/** Update all fuse states */
uint32_t ecl_fuse_update_all(const ecl_fuse_config_t *configs, uint32_t count);

/** Get degradation level (0=full, 1=reduced, 2=minimal, 3=emergency) */
uint32_t ecl_degrade_level(uint32_t dimension);

#ifdef __cplusplus
}
#endif

#endif /* ECLEXIA_FFI_H */
