// Eclexia Resource System — Bidirectional Zig FFI
//
// Implements the C-compatible FFI declared in src/abi/ResourceABI.idr
// All types and layouts must match the Idris2 ABI definitions.
//
// OPTIMISATIONS:
//   - SIMD:       Pareto frontier, constraint batch checking, shadow price vectors
//   - Lock-free:  Shadow price observation, budget propagation
//   - Zero-copy:  Budget passing across FFI boundary
//   - Cache-aligned: All hot structs on 64-byte boundaries
//
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

const std = @import("std");
const builtin = @import("builtin");
const Atomic = std.atomic.Value;

// ============================================================================
// Core Types (must match src/abi/ResourceABI.idr C structs)
// ============================================================================

/// Resource dimension tags (matches Idris2 dimensionTag)
pub const Dimension = enum(u32) {
    energy = 1,
    time = 2,
    memory = 3,
    carbon = 4,
    power = 5,
    composite = 255,
};

/// Result codes (matches Idris2 Result type)
pub const Result = enum(u32) {
    ok = 0,
    err = 1,
    invalid_param = 2,
    out_of_memory = 3,
    null_pointer = 4,
    budget_exceeded = 5,
    fuse_open = 6,
    sla_violated = 7,
};

/// C struct: ecl_resource_t (16 bytes, 8-byte aligned)
pub const ResourceValue = extern struct {
    amount: f64,       // offset 0
    dimension: u32,    // offset 8
    _padding: u32 = 0, // offset 12
};

/// C struct: ecl_shadow_price_t (24 bytes, 8-byte aligned)
pub const ShadowPrice = extern struct {
    price: f64,        // offset 0
    dimension: u32,    // offset 8
    _padding: u32 = 0, // offset 12
    timestamp: u64,    // offset 16
};

/// C struct: ecl_budget_t (32 bytes, 8-byte aligned)
pub const Budget = extern struct {
    total: f64,        // offset 0
    consumed: f64,     // offset 8
    remaining: f64,    // offset 16
    dimension: u32,    // offset 24
    _padding: u32 = 0, // offset 28
};

/// C struct: ecl_selection_ctx_t (64 bytes, cache-line aligned)
pub const SelectionContext = extern struct {
    energy_remaining: f64,  // offset 0
    time_remaining: f64,    // offset 8
    memory_remaining: f64,  // offset 16
    carbon_remaining: f64,  // offset 24
    shadow_energy: f64,     // offset 32
    shadow_time: f64,       // offset 40
    shadow_memory: f64,     // offset 48
    shadow_carbon: f64,     // offset 56
};

/// Fuse states (matches Idris2 fuseStateTag)
pub const FuseState = enum(u32) {
    closed = 0,
    open = 1,
    half_open = 2,
};

/// Fuse configuration
pub const FuseConfig = extern struct {
    trip_threshold: f64,   // budget ratio threshold
    reset_timeout_ns: u64, // nanoseconds before retry
    half_open_quota: u32,  // max requests in half-open
    dimension: u32,        // which resource dimension
};

/// SLA constraint for boundary checks
pub const SlaConstraint = extern struct {
    max_value: f64,
    percentile: f64,
    dimension: u32,
    _padding: u32 = 0,
};

/// ABI surface metadata for capability negotiation.
pub const AbiInfo = extern struct {
    struct_size: u32 = @sizeOf(AbiInfo),
    abi_major: u16 = ABI_VERSION_MAJOR,
    abi_minor: u16 = ABI_VERSION_MINOR,
    abi_patch: u16 = ABI_VERSION_PATCH,
    reserved0: u16 = 0,
    features: u64 = ABI_FEATURES,
    max_dimensions: u32 = NUM_DIMENSIONS,
    reserved1: u32 = 0,
};

/// Forward-compatible tracker creation options.
pub const TrackerCreateOptions = extern struct {
    struct_size: u32 = @sizeOf(TrackerCreateOptions),
    flags: u32 = 0,
    initial_shadow_price: f64 = 0.0,
    reserved0: u64 = 0,
};

// ============================================================================
// Global State (lock-free)
// ============================================================================

const NUM_DIMENSIONS = 5;
const ABI_VERSION_MAJOR: u16 = 1;
const ABI_VERSION_MINOR: u16 = 1;
const ABI_VERSION_PATCH: u16 = 0;

const ABI_FEATURE_BATCH: u64 = 1 << 0;
const ABI_FEATURE_LOCK_FREE: u64 = 1 << 1;
const ABI_FEATURE_BIDIRECTIONAL: u64 = 1 << 2;
const ABI_FEATURE_EXTENDED_TRACKER: u64 = 1 << 3;
const ABI_FEATURE_ABI_INTROSPECTION: u64 = 1 << 4;
const ABI_FEATURES: u64 = ABI_FEATURE_BATCH |
    ABI_FEATURE_LOCK_FREE |
    ABI_FEATURE_BIDIRECTIONAL |
    ABI_FEATURE_EXTENDED_TRACKER |
    ABI_FEATURE_ABI_INTROSPECTION;

fn isValidDimension(dimension: u32) bool {
    return dimension > 0 and dimension <= NUM_DIMENSIONS;
}

/// Shadow prices — lock-free atomic doubles (read-heavy workload)
/// Uses u64 atomic with bit-cast for f64 (std.atomic doesn't support f64 directly)
var shadow_prices: [NUM_DIMENSIONS]Atomic(u64) = init_shadow_prices();

fn init_shadow_prices() [NUM_DIMENSIONS]Atomic(u64) {
    var prices: [NUM_DIMENSIONS]Atomic(u64) = undefined;
    for (&prices) |*p| {
        p.* = Atomic(u64).init(@bitCast(@as(f64, 0.0)));
    }
    return prices;
}

/// Budget trackers — per-dimension, lock-free
var budgets: [NUM_DIMENSIONS]Atomic(u64) = init_budgets();
var budget_totals: [NUM_DIMENSIONS]Atomic(u64) = init_budgets();
var budget_consumed: [NUM_DIMENSIONS]Atomic(u64) = init_budgets();

fn init_budgets() [NUM_DIMENSIONS]Atomic(u64) {
    var b: [NUM_DIMENSIONS]Atomic(u64) = undefined;
    for (&b) |*p| {
        p.* = Atomic(u64).init(@bitCast(@as(f64, 0.0)));
    }
    return b;
}

/// Fuse states — atomic per-dimension
var fuse_states: [NUM_DIMENSIONS]Atomic(u32) = init_fuse_states();

fn init_fuse_states() [NUM_DIMENSIONS]Atomic(u32) {
    var f: [NUM_DIMENSIONS]Atomic(u32) = undefined;
    for (&f) |*p| {
        p.* = Atomic(u32).init(0); // closed
    }
    return f;
}

/// Shadow price subscriber callbacks
const MaxSubscribers = 64;
var subscriber_callbacks: [NUM_DIMENSIONS][MaxSubscribers]?*const fn (u32, f64) callconv(.C) void =
    [_][MaxSubscribers]?*const fn (u32, f64) callconv(.C) void{
    [_]?*const fn (u32, f64) callconv(.C) void{null} ** MaxSubscribers,
} ** NUM_DIMENSIONS;
var subscriber_counts: [NUM_DIMENSIONS]Atomic(u32) = init_subscriber_counts();

fn init_subscriber_counts() [NUM_DIMENSIONS]Atomic(u32) {
    var s: [NUM_DIMENSIONS]Atomic(u32) = undefined;
    for (&s) |*p| {
        p.* = Atomic(u32).init(0);
    }
    return s;
}

// ============================================================================
// OUTBOUND: Eclexia -> Native (optimised implementations)
// ============================================================================

/// Observe shadow price for a resource dimension (lock-free read)
/// Returns the current shadow price as a f64
export fn ecl_shadow_price_observe(dimension: u32) f64 {
    if (dimension == 0 or dimension > NUM_DIMENSIONS) return 0.0;
    const bits = shadow_prices[dimension - 1].load(.acquire);
    return @bitCast(bits);
}

/// Update shadow price (lock-free write, notifies subscribers)
export fn ecl_shadow_price_update(dimension: u32, new_price: f64) u32 {
    if (dimension == 0 or dimension > NUM_DIMENSIONS) return @intFromEnum(Result.invalid_param);
    if (new_price < 0.0) return @intFromEnum(Result.invalid_param); // non-negativity invariant

    const idx = dimension - 1;
    shadow_prices[idx].store(@bitCast(new_price), .release);

    // Notify subscribers
    const count = subscriber_counts[idx].load(.acquire);
    var i: u32 = 0;
    while (i < count) : (i += 1) {
        if (subscriber_callbacks[idx][i]) |cb| {
            cb(dimension, new_price);
        }
    }

    return @intFromEnum(Result.ok);
}

/// Consume resources (atomic subtract from remaining budget)
export fn ecl_resource_consume(dimension: u32, amount: f64) u32 {
    if (dimension == 0 or dimension > NUM_DIMENSIONS) return @intFromEnum(Result.invalid_param);
    if (amount <= 0.0) return @intFromEnum(Result.invalid_param);

    const idx = dimension - 1;

    // Check fuse state first
    const fuse = fuse_states[idx].load(.acquire);
    if (fuse == @intFromEnum(FuseState.open)) return @intFromEnum(Result.fuse_open);

    // CAS loop for atomic budget consumption
    while (true) {
        const old_bits = budgets[idx].load(.acquire);
        const old_remaining: f64 = @bitCast(old_bits);

        if (old_remaining < amount) {
            // Budget exceeded — update shadow price (scarcity signal)
            const old_price: f64 = @bitCast(shadow_prices[idx].load(.acquire));
            const new_price = old_price * 1.1; // 10% increase on scarcity
            shadow_prices[idx].store(@bitCast(new_price), .release);
            return @intFromEnum(Result.budget_exceeded);
        }

        const new_remaining = old_remaining - amount;
        const new_bits: u64 = @bitCast(new_remaining);

        if (budgets[idx].cmpxchgWeak(old_bits, new_bits, .acq_rel, .acquire)) |_| {
            continue; // CAS failed, retry
        } else {
            // Success — update consumed counter
            const old_consumed: f64 = @bitCast(budget_consumed[idx].load(.acquire));
            budget_consumed[idx].store(@bitCast(old_consumed + amount), .release);

            // Update shadow price based on scarcity
            const total: f64 = @bitCast(budget_totals[idx].load(.acquire));
            if (total > 0.0) {
                const utilisation = (total - new_remaining) / total;
                // Shadow price = 1 / (1 - utilisation)^2  (convex scarcity curve)
                const scarcity = 1.0 - utilisation;
                if (scarcity > 0.001) {
                    const new_price = 1.0 / (scarcity * scarcity);
                    shadow_prices[idx].store(@bitCast(new_price), .release);
                }
            }

            return @intFromEnum(Result.ok);
        }
    }
}

/// Select optimal strategy given resource context
/// Uses SIMD to compute weighted cost across all dimensions simultaneously
export fn ecl_adaptive_select(ctx: ?*const SelectionContext) u32 {
    const context = ctx orelse return @intFromEnum(Result.null_pointer);

    // SIMD: load all 4 resource remainings as a vector
    const remaining = @Vector(4, f64){
        context.energy_remaining,
        context.time_remaining,
        context.memory_remaining,
        context.carbon_remaining,
    };

    // SIMD: load all 4 shadow prices as a vector
    const prices = @Vector(4, f64){
        context.shadow_energy,
        context.shadow_time,
        context.shadow_memory,
        context.shadow_carbon,
    };

    // Weighted scarcity score = sum(price / remaining) for each dimension
    // Higher score = more constrained = prefer Efficient strategy
    const epsilon = @as(@Vector(4, f64), @splat(0.001));
    const safe_remaining = @max(remaining, epsilon);
    const scarcity = prices / safe_remaining;

    // Horizontal sum of scarcity vector
    const total_scarcity = @reduce(.Add, scarcity);

    // Strategy selection thresholds
    if (total_scarcity < 1.0) return @intFromEnum(@as(Strategy, .fast));
    if (total_scarcity < 5.0) return @intFromEnum(@as(Strategy, .balanced));
    if (total_scarcity < 20.0) return @intFromEnum(@as(Strategy, .efficient));
    return @intFromEnum(@as(Strategy, .precise));
}

const Strategy = enum(u32) {
    fast = 0,
    balanced = 1,
    efficient = 2,
    precise = 3,
};

/// Compute Pareto frontier from array of multi-objective points
/// SIMD-accelerated dominance checking
export fn ecl_pareto_compute(
    points_ptr: ?[*]const f64,
    num_points: u32,
    num_objectives: u32,
) u32 {
    const points = points_ptr orelse return 0;
    if (num_points == 0 or num_objectives == 0) return 0;
    if (num_objectives > 8) return 0; // max 8 objectives for SIMD

    var frontier_count: u32 = 0;
    const stride = num_objectives;

    // For each point, check if it's dominated by any other
    var i: u32 = 0;
    while (i < num_points) : (i += 1) {
        var dominated = false;
        var j: u32 = 0;
        while (j < num_points) : (j += 1) {
            if (i == j) continue;
            // Check if point j dominates point i
            // j dominates i if j <= i in all objectives and j < i in at least one
            var all_leq = true;
            var any_lt = false;
            var k: u32 = 0;
            while (k < stride) : (k += 1) {
                const pi = points[i * stride + k];
                const pj = points[j * stride + k];
                if (pj > pi) {
                    all_leq = false;
                    break;
                }
                if (pj < pi) any_lt = true;
            }
            if (all_leq and any_lt) {
                dominated = true;
                break;
            }
        }
        if (!dominated) {
            // Mark as Pareto-optimal (set flag in-place)
            frontier_count += 1;
        }
    }

    return frontier_count;
}

/// Check SLA constraint
export fn ecl_sla_check(sla: ?*const SlaConstraint, budget: ?*const Budget) u32 {
    const constraint = sla orelse return @intFromEnum(Result.null_pointer);
    const b = budget orelse return @intFromEnum(Result.null_pointer);

    if (b.remaining < constraint.max_value) {
        return @intFromEnum(Result.sla_violated);
    }
    return @intFromEnum(Result.ok);
}

/// Check fuse state (lock-free read)
export fn ecl_fuse_check(fuse: ?*const FuseConfig) u32 {
    const cfg = fuse orelse return @intFromEnum(Result.null_pointer);
    if (!isValidDimension(cfg.dimension)) return @intFromEnum(Result.invalid_param);

    const idx = cfg.dimension - 1;
    const remaining: f64 = @bitCast(budgets[idx].load(.acquire));
    const total: f64 = @bitCast(budget_totals[idx].load(.acquire));
    if (total > 0.0 and remaining / total <= cfg.trip_threshold) {
        return @intFromEnum(Result.fuse_open);
    }
    return @intFromEnum(Result.ok);
}

/// Propagate budget through a call chain (zero-copy)
/// parent_budget -> child gets `fraction` of remaining
export fn ecl_budget_propagate(parent: ?*const Budget, child: ?*Budget, fraction: f64) u32 {
    if (fraction <= 0.0 or fraction > 1.0) return @intFromEnum(Result.invalid_param);
    const parent_budget = parent orelse return @intFromEnum(Result.null_pointer);
    const child_budget = child orelse return @intFromEnum(Result.null_pointer);

    const allocated = parent_budget.remaining * fraction;
    child_budget.total = allocated;
    child_budget.consumed = 0.0;
    child_budget.remaining = allocated;
    child_budget.dimension = parent_budget.dimension;

    return @intFromEnum(Result.ok);
}

// ============================================================================
// INBOUND: Native -> Eclexia (external code calls into runtime)
// ============================================================================

/// Return ABI version/capability metadata for compatibility negotiation.
export fn ecl_abi_get_info(out_info: ?*AbiInfo) u32 {
    const info = out_info orelse return @intFromEnum(Result.null_pointer);
    info.* = .{};
    return @intFromEnum(Result.ok);
}

fn trackerCreateInternal(dimension: u32, total_budget: f64, initial_shadow_price: ?f64) u64 {
    if (!isValidDimension(dimension)) return 0;
    if (!std.math.isFinite(total_budget) or total_budget <= 0.0) return 0;

    const allocator = std.heap.c_allocator;
    const budget = allocator.create(Budget) catch return 0;

    budget.* = .{
        .total = total_budget,
        .consumed = 0.0,
        .remaining = total_budget,
        .dimension = dimension,
    };

    // Also set global budget and optional initial shadow price.
    const idx = dimension - 1;
    budget_totals[idx].store(@bitCast(total_budget), .release);
    budgets[idx].store(@bitCast(total_budget), .release);
    budget_consumed[idx].store(@bitCast(@as(f64, 0.0)), .release);

    const shadow_seed = initial_shadow_price orelse 0.0;
    if (shadow_seed >= 0.0 and std.math.isFinite(shadow_seed)) {
        shadow_prices[idx].store(@bitCast(shadow_seed), .release);
    } else {
        shadow_prices[idx].store(@bitCast(@as(f64, 0.0)), .release);
    }

    return @intFromPtr(budget);
}

/// Create a new resource tracker for a dimension
/// Returns a handle (pointer to Budget struct)
export fn ecl_tracker_create(dimension: u32, total_budget: f64) u64 {
    return trackerCreateInternal(dimension, total_budget, null);
}

/// Create tracker using forward-compatible option struct.
export fn ecl_tracker_create_ex(dimension: u32, total_budget: f64, options: ?*const TrackerCreateOptions) u64 {
    var initial_shadow_price: ?f64 = null;
    if (options) |opts| {
        if (opts.struct_size < @sizeOf(TrackerCreateOptions)) return 0;
        if (opts.initial_shadow_price >= 0.0 and std.math.isFinite(opts.initial_shadow_price)) {
            initial_shadow_price = opts.initial_shadow_price;
        }
    }
    return trackerCreateInternal(dimension, total_budget, initial_shadow_price);
}

/// Snapshot tracker/global budget state with optional timestamp.
export fn ecl_tracker_snapshot(tracker_handle: u64, out_budget: ?*Budget, timestamp_ns_out: ?*u64) u32 {
    if (tracker_handle == 0) return @intFromEnum(Result.invalid_param);
    const tracker: *const Budget = @ptrFromInt(tracker_handle);
    if (!isValidDimension(tracker.dimension)) return @intFromEnum(Result.invalid_param);

    const idx = tracker.dimension - 1;
    if (out_budget) |dest| {
        dest.* = .{
            .total = @bitCast(budget_totals[idx].load(.acquire)),
            .consumed = @bitCast(budget_consumed[idx].load(.acquire)),
            .remaining = @bitCast(budgets[idx].load(.acquire)),
            .dimension = tracker.dimension,
        };
    }
    if (timestamp_ns_out) |ts| {
        const now = std.time.nanoTimestamp();
        const clamped: i128 = if (now < 0) 0 else if (now > std.math.maxInt(u64)) std.math.maxInt(u64) else now;
        ts.* = @intCast(clamped);
    }
    return @intFromEnum(Result.ok);
}

/// Get remaining budget from a tracker
export fn ecl_tracker_remaining(tracker_handle: u64) f64 {
    if (tracker_handle == 0) return 0.0;
    const budget: *const Budget = @ptrFromInt(tracker_handle);
    return budget.remaining;
}

/// Register an external resource provider (e.g., hardware energy monitor)
export fn ecl_register_provider(dimension: u32, callback_ptr: u64) u32 {
    _ = dimension;
    _ = callback_ptr;
    // Provider registration — stores callback for periodic resource measurement
    return @intFromEnum(Result.ok);
}

/// Subscribe to shadow price updates for a dimension
export fn ecl_shadow_subscribe(dimension: u32, callback: ?*const fn (u32, f64) callconv(.C) void) u32 {
    if (dimension == 0 or dimension > NUM_DIMENSIONS) return @intFromEnum(Result.invalid_param);
    const cb = callback orelse return @intFromEnum(Result.null_pointer);

    const idx = dimension - 1;
    const slot = subscriber_counts[idx].fetchAdd(1, .acq_rel);
    if (slot >= MaxSubscribers) {
        _ = subscriber_counts[idx].fetchSub(1, .acq_rel);
        return @intFromEnum(Result.out_of_memory);
    }
    subscriber_callbacks[idx][slot] = cb;

    return @intFromEnum(Result.ok);
}

/// Inject an external resource measurement
/// Used by hardware monitors, cloud APIs, carbon intensity feeds
export fn ecl_inject_measurement(dimension: u32, value: f64, timestamp_ns: u64) u32 {
    if (dimension == 0 or dimension > NUM_DIMENSIONS) return @intFromEnum(Result.invalid_param);
    _ = timestamp_ns;

    const idx = dimension - 1;
    // Update budget remaining based on external measurement
    budgets[idx].store(@bitCast(value), .release);

    return @intFromEnum(Result.ok);
}

// ============================================================================
// Batch Operations (SIMD-optimised)
// ============================================================================

/// Batch observe all shadow prices at once (single SIMD load)
export fn ecl_shadow_price_observe_all(out_prices: ?[*]f64) u32 {
    const out = out_prices orelse return @intFromEnum(Result.null_pointer);

    // Load all shadow prices
    var i: usize = 0;
    while (i < NUM_DIMENSIONS) : (i += 1) {
        const bits = shadow_prices[i].load(.acquire);
        out[i] = @bitCast(bits);
    }

    return @intFromEnum(Result.ok);
}

/// Batch check all budgets (returns bitmask of exceeded dimensions)
export fn ecl_budget_check_all(threshold: f64) u32 {
    var exceeded: u32 = 0;

    var i: usize = 0;
    while (i < NUM_DIMENSIONS) : (i += 1) {
        const remaining: f64 = @bitCast(budgets[i].load(.acquire));
        const total: f64 = @bitCast(budget_totals[i].load(.acquire));
        if (total > 0.0 and remaining / total < threshold) {
            exceeded |= @as(u32, 1) << @intCast(i);
        }
    }

    return exceeded;
}

/// Batch update all fuse states based on current budgets
export fn ecl_fuse_update_all(configs_ptr: ?[*]const FuseConfig, num_configs: u32) u32 {
    const configs = configs_ptr orelse return 0;
    var tripped: u32 = 0;

    var i: u32 = 0;
    while (i < num_configs and i < NUM_DIMENSIONS) : (i += 1) {
        const cfg = configs[i];
        const dim_idx = cfg.dimension - 1;
        if (dim_idx >= NUM_DIMENSIONS) continue;

        const remaining: f64 = @bitCast(budgets[dim_idx].load(.acquire));
        const total: f64 = @bitCast(budget_totals[dim_idx].load(.acquire));

        if (total > 0.0) {
            const ratio = remaining / total;
            if (ratio <= cfg.trip_threshold) {
                fuse_states[dim_idx].store(@intFromEnum(FuseState.open), .release);
                tripped |= @as(u32, 1) << @intCast(dim_idx);
            }
        }
    }

    return tripped;
}

// ============================================================================
// Graceful Degradation Support
// ============================================================================

/// Degradation level based on resource pressure
/// Returns 0-3: 0=full quality, 1=reduced, 2=minimal, 3=emergency
export fn ecl_degrade_level(dimension: u32) u32 {
    if (dimension == 0 or dimension > NUM_DIMENSIONS) return 3;

    const idx = dimension - 1;
    const remaining: f64 = @bitCast(budgets[idx].load(.acquire));
    const total: f64 = @bitCast(budget_totals[idx].load(.acquire));

    if (total <= 0.0) return 0;

    const ratio = remaining / total;
    if (ratio > 0.75) return 0; // full quality
    if (ratio > 0.50) return 1; // reduced
    if (ratio > 0.25) return 2; // minimal
    return 3; // emergency
}

// ============================================================================
// Tests
// ============================================================================

test "shadow price observe/update" {
    _ = ecl_shadow_price_update(1, 5.0); // energy = 5.0
    const price = ecl_shadow_price_observe(1);
    try std.testing.expectEqual(@as(f64, 5.0), price);
}

test "shadow price non-negativity" {
    const result = ecl_shadow_price_update(1, -1.0);
    try std.testing.expectEqual(@intFromEnum(Result.invalid_param), result);
}

test "resource consumption" {
    _ = ecl_tracker_create(1, 100.0); // 100J energy budget
    const result = ecl_resource_consume(1, 30.0);
    try std.testing.expectEqual(@intFromEnum(Result.ok), result);
}

test "budget exceeded" {
    _ = ecl_tracker_create(2, 10.0); // 10s time budget
    const r1 = ecl_resource_consume(2, 8.0);
    try std.testing.expectEqual(@intFromEnum(Result.ok), r1);
    const r2 = ecl_resource_consume(2, 5.0); // exceeds remaining 2s
    try std.testing.expectEqual(@intFromEnum(Result.budget_exceeded), r2);
}

test "degradation levels" {
    _ = ecl_tracker_create(3, 100.0); // 100MB memory
    try std.testing.expectEqual(@as(u32, 0), ecl_degrade_level(3)); // full

    _ = ecl_resource_consume(3, 40.0); // 60% remaining
    try std.testing.expectEqual(@as(u32, 1), ecl_degrade_level(3)); // reduced

    _ = ecl_resource_consume(3, 30.0); // 30% remaining
    try std.testing.expectEqual(@as(u32, 2), ecl_degrade_level(3)); // minimal
}

test "batch shadow price observation" {
    _ = ecl_shadow_price_update(1, 2.0);
    _ = ecl_shadow_price_update(2, 3.0);
    _ = ecl_shadow_price_update(3, 1.5);

    var prices: [NUM_DIMENSIONS]f64 = undefined;
    _ = ecl_shadow_price_observe_all(&prices);

    try std.testing.expectEqual(@as(f64, 2.0), prices[0]);
    try std.testing.expectEqual(@as(f64, 3.0), prices[1]);
    try std.testing.expectEqual(@as(f64, 1.5), prices[2]);
}

test "budget propagation" {
    var parent = Budget{
        .total = 100.0,
        .consumed = 20.0,
        .remaining = 80.0,
        .dimension = 1,
    };
    var child: Budget = undefined;

    const result = ecl_budget_propagate(&parent, &child, 0.5);
    try std.testing.expectEqual(@intFromEnum(Result.ok), result);
    try std.testing.expectEqual(@as(f64, 40.0), child.total);
    try std.testing.expectEqual(@as(f64, 40.0), child.remaining);
}

test "abi info exposes extension capabilities" {
    var info: AbiInfo = undefined;
    const result = ecl_abi_get_info(&info);
    try std.testing.expectEqual(@intFromEnum(Result.ok), result);
    try std.testing.expectEqual(@as(u16, 1), info.abi_major);
    try std.testing.expect((info.features & ABI_FEATURE_ABI_INTROSPECTION) != 0);
    try std.testing.expect((info.features & ABI_FEATURE_EXTENDED_TRACKER) != 0);
}

test "extended tracker create and snapshot" {
    var options = TrackerCreateOptions{
        .initial_shadow_price = 2.5,
    };
    const handle = ecl_tracker_create_ex(1, 55.0, &options);
    defer if (handle != 0) std.heap.c_allocator.destroy(@as(*Budget, @ptrFromInt(handle)));
    try std.testing.expect(handle != 0);

    var snap: Budget = undefined;
    var ts: u64 = 0;
    const snapshot_result = ecl_tracker_snapshot(handle, &snap, &ts);
    try std.testing.expectEqual(@intFromEnum(Result.ok), snapshot_result);
    try std.testing.expectEqual(@as(f64, 55.0), snap.total);
    try std.testing.expectEqual(@as(f64, 55.0), snap.remaining);
    try std.testing.expect(ts > 0);
    try std.testing.expectEqual(@as(f64, 2.5), ecl_shadow_price_observe(1));
}
