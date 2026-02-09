// Eclexia Resource System — FFI Build Configuration
//
// Builds libeclexia_ffi (.so/.dylib/.dll) and static (.a) library.
// Includes SIMD-optimised resource tracking, lock-free shadow prices,
// and bidirectional FFI for the Eclexia runtime.
//
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // Shared library (.so, .dylib, .dll)
    const lib = b.addSharedLibrary(.{
        .name = "eclexia_ffi",
        .root_source_file = b.path("src/resource.zig"),
        .target = target,
        .optimize = optimize,
    });
    lib.version = .{ .major = 0, .minor = 1, .patch = 0 };

    // Static library (.a)
    const lib_static = b.addStaticLibrary(.{
        .name = "eclexia_ffi",
        .root_source_file = b.path("src/resource.zig"),
        .target = target,
        .optimize = optimize,
    });

    // Install artifacts
    b.installArtifact(lib);
    b.installArtifact(lib_static);

    // Unit tests
    const lib_tests = b.addTest(.{
        .root_source_file = b.path("src/resource.zig"),
        .target = target,
        .optimize = optimize,
    });

    const run_lib_tests = b.addRunArtifact(lib_tests);

    const test_step = b.step("test", "Run resource FFI unit tests");
    test_step.dependOn(&run_lib_tests.step);
}
