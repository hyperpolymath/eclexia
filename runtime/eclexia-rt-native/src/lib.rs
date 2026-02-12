// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Native runtime library for Eclexia LLVM backend.
//!
//! Provides C-compatible implementations of the runtime symbols referenced
//! in the LLVM IR output. These functions handle resource tracking, shadow
//! price queries, and runtime lifecycle management.
//!
//! ## Symbols provided
//!
//! - `__eclexia_runtime_start_tracking()` - Initialize resource tracking context
//! - `__eclexia_runtime_stop_tracking(ctx)` - Finalize and print resource summary
//! - `__eclexia_track_resource(ctx, amount)` - Record resource consumption
//! - `__eclexia_query_shadow_price(ctx)` - Query current shadow price
//! - `__eclexia_range(start, end, inclusive)` - Create a range object
//!
//! ## Linking
//!
//! Build as a static library and link with LLVM-compiled Eclexia programs:
//! ```bash
//! llc -O2 output.ll -filetype=obj -o output.o
//! cc output.o -L target/release -leclexia_rt_native -o output
//! ```

use std::collections::HashMap;
use std::ffi::c_void;
use std::time::Instant;

/// Resource tracking context.
struct TrackingContext {
    start_time: Instant,
    total_energy: f64,
    resource_counts: HashMap<String, f64>,
    shadow_prices: HashMap<String, f64>,
}

impl TrackingContext {
    fn new() -> Self {
        Self {
            start_time: Instant::now(),
            total_energy: 0.0,
            resource_counts: HashMap::new(),
            shadow_prices: HashMap::from([
                ("energy".to_string(), 0.000033),
                ("time".to_string(), 0.001),
                ("memory".to_string(), 0.0000001),
                ("carbon".to_string(), 0.00005),
            ]),
        }
    }
}

/// Range object for iteration.
#[repr(C)]
pub struct Range {
    start: i64,
    end: i64,
    inclusive: bool,
}

/// Initialize a resource tracking context.
///
/// Returns an opaque pointer to the context.
#[no_mangle]
pub extern "C" fn __eclexia_runtime_start_tracking() -> *mut c_void {
    let ctx = Box::new(TrackingContext::new());
    let ptr = Box::into_raw(ctx) as *mut c_void;
    ptr
}

/// Finalize resource tracking and print summary.
#[no_mangle]
pub extern "C" fn __eclexia_runtime_stop_tracking(ctx: *mut c_void) {
    if ctx.is_null() {
        return;
    }

    let ctx = unsafe { Box::from_raw(ctx as *mut TrackingContext) };
    let elapsed = ctx.start_time.elapsed();

    eprintln!("[eclexia-rt] Resource tracking summary:");
    eprintln!("  Elapsed: {:.3}ms", elapsed.as_secs_f64() * 1000.0);
    eprintln!("  Total energy: {:.6}", ctx.total_energy);

    for (name, amount) in &ctx.resource_counts {
        eprintln!("  {}: {:.6}", name, amount);
    }
}

/// Record resource consumption.
///
/// `ctx` is the tracking context pointer.
/// `amount` is the resource amount consumed.
#[no_mangle]
pub extern "C" fn __eclexia_track_resource(ctx: *mut c_void, amount: f64) {
    if ctx.is_null() {
        return;
    }

    let ctx = unsafe { &mut *(ctx as *mut TrackingContext) };
    ctx.total_energy += amount;
    *ctx.resource_counts.entry("energy".to_string()).or_insert(0.0) += amount;
}

/// Query the current shadow price for a resource.
///
/// Returns the shadow price as f64. Currently returns the default
/// shadow price for energy (0.000033).
#[no_mangle]
pub extern "C" fn __eclexia_query_shadow_price(ctx: *mut c_void) -> f64 {
    if ctx.is_null() {
        return 0.000033; // default energy shadow price
    }

    let ctx = unsafe { &*(ctx as *const TrackingContext) };
    *ctx.shadow_prices.get("energy").unwrap_or(&0.000033)
}

/// Create a range object.
///
/// Returns a pointer to a heap-allocated Range struct.
#[no_mangle]
pub extern "C" fn __eclexia_range(start: i64, end: i64, inclusive: bool) -> *mut Range {
    let range = Box::new(Range {
        start,
        end,
        inclusive,
    });
    Box::into_raw(range)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tracking_lifecycle() {
        let ctx = __eclexia_runtime_start_tracking();
        assert!(!ctx.is_null());

        __eclexia_track_resource(ctx, 1.5);
        __eclexia_track_resource(ctx, 2.5);

        let price = __eclexia_query_shadow_price(ctx);
        assert!((price - 0.000033).abs() < 1e-10);

        // Stop prints summary to stderr
        __eclexia_runtime_stop_tracking(ctx);
    }

    #[test]
    fn test_null_context_safety() {
        // All functions should handle null safely
        __eclexia_runtime_stop_tracking(std::ptr::null_mut());
        __eclexia_track_resource(std::ptr::null_mut(), 1.0);
        let price = __eclexia_query_shadow_price(std::ptr::null_mut());
        assert!((price - 0.000033).abs() < 1e-10);
    }

    #[test]
    fn test_range_creation() {
        let range = __eclexia_range(0, 10, false);
        assert!(!range.is_null());
        let r = unsafe { &*range };
        assert_eq!(r.start, 0);
        assert_eq!(r.end, 10);
        assert!(!r.inclusive);
        unsafe { drop(Box::from_raw(range)) };

        let range_incl = __eclexia_range(1, 5, true);
        let r = unsafe { &*range_incl };
        assert_eq!(r.start, 1);
        assert_eq!(r.end, 5);
        assert!(r.inclusive);
        unsafe { drop(Box::from_raw(range_incl)) };
    }
}
