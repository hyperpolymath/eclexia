# Resource-Aware Programming with Eclexia

**Target Audience:** Intermediate - completed Getting Started tutorial
**Estimated Time:** 3-4 hours
**Prerequisites:** Basic Eclexia syntax, resources, dimensional types

---

## Table of Contents

1. [Introduction to Resource-Aware Computing](#introduction-to-resource-aware-computing)
2. [Multi-Resource Management](#multi-resource-management)
3. [Adaptive Execution](#adaptive-execution)
4. [Carbon-Aware Scheduling](#carbon-aware-scheduling)
5. [Battery-Conscious Mobile Apps](#battery-conscious-mobile-apps)
6. [Cost-Optimized Cloud Services](#cost-optimized-cloud-services)
7. [Real-Time Resource Constraints](#real-time-resource-constraints)
8. [Advanced Patterns](#advanced-patterns)
9. [Performance and Profiling](#performance-and-profiling)
10. [Best Practices](#best-practices)

---

## Introduction to Resource-Aware Computing

### The Resource Crisis

Modern computing faces a **resource trilemma**:
1. **Performance** - Users want fast, responsive applications
2. **Efficiency** - Data centers consume 1-2% of global electricity
3. **Cost** - Cloud bills scale with compute usage

Traditional programming treats resources as infinite. Eclexia makes them **explicit and manageable**.

### Why Resource-Aware?

**Example: Image Processing Service**

Traditional approach (Python):
```python
def process_image(image):
    return apply_ml_model(image)  # Cost: ???
```

Problems:
- Unknown energy cost (could drain mobile battery)
- Unknown time cost (might timeout)
- Unknown $ cost (cloud bill surprise)

**Eclexia approach:**
```eclexia
resource energy { budget: 500J }
resource time { budget: 100ms }
resource money { budget: 0.01USD }

fn process_image(image: Image) -> Result<Image, String>
    @requires(energy: 400J, time: 80ms, money: 0.008USD)
{
    adaptive process {
        ml_model: {
            apply_ml_model(image)
            @requires(energy: 400J, time: 80ms, money: 0.008USD)
        },
        simple: {
            apply_filters(image)
            @requires(energy: 50J, time: 20ms, money: 0.001USD)
        },
    }
}
```

Benefits:
- **Budgets prevent overruns** - If you only have 100J battery left, ML model won't run
- **Adaptive fallback** - Gracefully degrades to simpler algorithm
- **Predictable costs** - Know exactly what you're spending

---

## Multi-Resource Management

### Declaring Multiple Resources

Most applications need to track multiple resources simultaneously:

```eclexia
resource energy {
    dimension: Energy,
    budget: 1000J,
    shadow: compute_energy_price(),
}

resource time {
    dimension: Time,
    budget: 500ms,
    shadow: compute_time_price(),
}

resource memory {
    dimension: Information,
    budget: 100MB,
    shadow: compute_memory_price(),
}
```

### Resource Dependencies

Some resources are **interdependent**. For example, more time usually costs more energy:

```eclexia
/// Compute-intensive task
fn matrix_multiply(a: Matrix, b: Matrix) -> Matrix
    @requires(time: 100ms, energy: 200J)
{
    // Energy consumption scales with time
    // 200J ≈ 2W * 100ms
    // ...
}
```

### Resource Tradeoffs

Often you can trade one resource for another:

```eclexia
adaptive compress {
    // Fast but memory-hungry
    fast: {
        lz4_compress(data)
        @requires(time: 10ms, memory: 50MB)
    },
    // Slow but memory-efficient
    slow: {
        gzip_compress(data)
        @requires(time: 100ms, memory: 5MB)
    },
}
```

If you have plenty of memory but limited time, Eclexia chooses `fast`. If memory is scarce, it chooses `slow`.

### Shadow Prices Guide Selection

Shadow prices make tradeoffs explicit:

```eclexia
resource time {
    budget: 100ms,
    shadow: compute_time_price(),
}

resource memory {
    budget: 20MB,
    shadow: compute_memory_price(),
}

// At start: time.shadow ≈ 0.1, memory.shadow ≈ 0.1
// Cost of fast: 0.1 * 10ms + 0.1 * 50MB = 1 + 5 = 6
// Cost of slow: 0.1 * 100ms + 0.1 * 5MB = 10 + 0.5 = 10.5
// Choose fast (lower cost)

// After using 90ms: time.shadow ≈ 9.0, memory.shadow ≈ 0.1
// Cost of fast: 9.0 * 10ms + 0.1 * 50MB = 90 + 5 = 95
// Cost of slow: 9.0 * 100ms + 0.1 * 5MB = 900 + 0.5 = 900.5
// Choose fast (still lower, barely fits budget)

// After using 95ms: time.shadow ≈ 19.0
// fast would exceed budget (needs 10ms, only 5ms left)
// Must choose slow or fail
```

---

## Adaptive Execution

### Basic Adaptive Blocks

Adaptive blocks provide **multiple implementations** ranked by cost:

```eclexia
adaptive sort {
    quicksort: {
        quicksort(data) @requires(time: 10ms)
    },
    mergesort: {
        mergesort(data) @requires(time: 15ms)
    },
    bubblesort: {
        bubblesort(data) @requires(time: 100ms)
    },
}
```

Eclexia automatically:
1. **Evaluates costs** - Checks each implementation's shadow price
2. **Checks feasibility** - Ensures budget isn't exceeded
3. **Selects optimal** - Chooses lowest-cost feasible option

### Multi-Dimensional Adaptation

Real algorithms have multiple resource dimensions:

```eclexia
adaptive image_resize {
    gpu: {
        gpu_resize(image)
        @requires(time: 5ms, energy: 100J, memory: 200MB)
    },
    cpu_simd: {
        cpu_simd_resize(image)
        @requires(time: 20ms, energy: 40J, memory: 50MB)
    },
    cpu_basic: {
        cpu_basic_resize(image)
        @requires(time: 100ms, energy: 20J, memory: 10MB)
    },
}
```

Selection depends on **current shadow prices**:
- **Desktop PC** (unlimited power): GPU wins (fastest)
- **Mobile phone** (battery constrained): CPU basic wins (lowest energy)
- **Embedded device** (limited memory): CPU basic wins (smallest memory)

### Nested Adaptive Blocks

Adaptation can be hierarchical:

```eclexia
adaptive video_encode {
    high_quality: {
        adaptive codec {
            av1: { av1_encode(video) @requires(time: 500ms, energy: 1000J) },
            h265: { h265_encode(video) @requires(time: 200ms, energy: 400J) },
        }
    },
    medium_quality: {
        h264_encode(video) @requires(time: 100ms, energy: 200J)
    },
    low_quality: {
        vp8_encode(video) @requires(time: 50ms, energy: 100J)
    },
}
```

First selects quality tier, then selects codec within that tier.

### Fallback Chains

Sometimes you want **explicit fallback order**:

```eclexia
fn fetch_data(url: String) -> Result<Data, String> {
    adaptive fetch {
        cache: {
            match cache.get(url) {
                Some(data) => Ok(data),
                None => Err("Cache miss"),
            }
            @requires(time: 1ms, energy: 1J)
        },
        network: {
            http_get(url) @requires(time: 100ms, energy: 500J)
        },
    }
}
```

Tries cache first (cheap), falls back to network (expensive) if cache misses.

---

## Carbon-Aware Scheduling

### The Carbon Intensity Problem

Electricity's carbon footprint varies by:
- **Time of day** - Solar power peaks at noon
- **Location** - Renewable vs. coal grids
- **Weather** - Wind turbines produce more on windy days

**Example:** Training an AI model

- **At 2 PM** (solar peak): 50g CO₂/kWh
- **At 8 PM** (coal peak): 500g CO₂/kWh

**10x difference** for the same computation!

### Carbon as a Resource

Model carbon emissions as a resource:

```eclexia
resource carbon {
    dimension: Mass,  // kg CO₂
    budget: 1kg,
    shadow: get_carbon_intensity(),  // $/kg CO₂
}
```

### Dynamic Carbon Pricing

Fetch real-time carbon intensity:

```eclexia
fn get_carbon_intensity() -> Float {
    // Call carbon intensity API (e.g., ElectricityMaps, WattTime)
    let api_response = http_get("https://api.electricitymaps.com/v3/carbon-intensity/latest");
    let intensity = parse_json(api_response)["carbonIntensity"];

    // Convert g/kWh to $/kg (assuming $50/ton carbon price)
    intensity * 0.00005
}
```

### Scheduling Workloads

Defer non-urgent work to low-carbon periods:

```eclexia
fn schedule_training(model: Model, dataset: Dataset) {
    resource carbon {
        budget: 10kg,
        shadow: get_carbon_intensity(),
    }

    adaptive train {
        now: {
            if carbon.shadow_price < 0.01 {  // Low carbon intensity
                train_model(model, dataset)
                @requires(carbon: 5kg, time: 2h)
            } else {
                Err("Carbon intensity too high")
            }
        },
        deferred: {
            schedule_for_later(train_model, model, dataset)
            @requires(carbon: 0kg, time: 1ms)  // Just scheduling, not training
        },
    }
}
```

### Geographic Load Shifting

Run compute where renewable energy is abundant:

```eclexia
adaptive compute {
    us_west: {
        run_on_region("us-west-1", task)
        @requires(carbon: 2kg)  // High solar penetration
    },
    europe: {
        run_on_region("eu-central-1", task)
        @requires(carbon: 5kg)  // Mixed grid
    },
    us_east: {
        run_on_region("us-east-1", task)
        @requires(carbon: 8kg)  // More coal
    },
}
```

Eclexia automatically routes to the lowest-carbon region.

---

## Battery-Conscious Mobile Apps

### Battery as a Resource

Mobile devices have **finite energy budgets**:

```eclexia
resource battery {
    dimension: Energy,
    budget: get_remaining_battery(),  // Dynamic
    shadow: compute_battery_price(),
}

fn get_remaining_battery() -> Energy {
    // Platform-specific battery API
    let percent = platform_battery_level();
    let capacity = 3000mAh * 3.7V;  // Typical smartphone
    capacity * percent
}
```

### Adaptive UI Rendering

Reduce quality when battery is low:

```eclexia
fn render_frame(scene: Scene) {
    resource battery { budget: get_remaining_battery() }

    adaptive render {
        high_quality: {
            if battery.remaining() > 10000J {
                render_4k(scene) @requires(battery: 50J)
            } else {
                Err("Battery too low for 4K")
            }
        },
        medium_quality: {
            render_1080p(scene) @requires(battery: 20J)
        },
        low_quality: {
            render_720p(scene) @requires(battery: 10J)
        },
    }
}
```

### Background Task Management

Defer expensive tasks:

```eclexia
fn sync_photos() {
    resource battery { budget: get_remaining_battery() }

    adaptive sync {
        full_sync: {
            if battery.remaining() > 50000J && is_charging() {
                upload_all_photos() @requires(battery: 30000J)
            } else {
                Err("Not enough battery or not charging")
            }
        },
        partial_sync: {
            upload_recent_photos() @requires(battery: 5000J)
        },
        skip: {
            schedule_for_later(sync_photos)
            @requires(battery: 0J)
        },
    }
}
```

### Network Efficiency

WiFi is 10x more energy-efficient than cellular:

```eclexia
adaptive download {
    wifi: {
        if is_wifi_available() {
            download_over_wifi(file)
            @requires(battery: 100J, time: 5s)
        } else {
            Err("WiFi not available")
        }
    },
    cellular: {
        download_over_cellular(file)
        @requires(battery: 1000J, time: 10s)
    },
    deferred: {
        schedule_for_wifi(file)
        @requires(battery: 1J, time: 1ms)
    },
}
```

---

## Cost-Optimized Cloud Services

### Cloud Pricing as Resources

Model AWS/GCP pricing:

```eclexia
resource money {
    dimension: Currency,  // USD
    budget: 1.00USD,
    shadow: 1.0,  // $1 = $1
}

resource compute {
    dimension: ComputeUnits,
    budget: 1000CU,
    shadow: 0.0001,  // $0.0001 per compute unit
}
```

### Serverless Function Optimization

Choose instance types by cost:

```eclexia
adaptive lambda {
    arm_graviton: {
        run_on_architecture("arm64", task)
        @requires(money: 0.0000166USD, time: 1s)  // 20% cheaper
    },
    x86: {
        run_on_architecture("x86_64", task)
        @requires(money: 0.0000208USD, time: 1s)
    },
}
```

### Spot Instance Bidding

Use spot instances when possible:

```eclexia
adaptive instance {
    spot: {
        let price = get_spot_price("c5.xlarge");
        if price < 0.05 {
            run_on_spot("c5.xlarge", task)
            @requires(money: price * 1h)
        } else {
            Err("Spot price too high")
        }
    },
    on_demand: {
        run_on_demand("c5.xlarge", task)
        @requires(money: 0.17USD)  // Full price
    },
}
```

### Multi-Cloud Optimization

Arbitrage across cloud providers:

```eclexia
adaptive cloud {
    aws: {
        run_on_aws(task) @requires(money: 0.10USD, time: 100ms)
    },
    gcp: {
        run_on_gcp(task) @requires(money: 0.08USD, time: 120ms)
    },
    azure: {
        run_on_azure(task) @requires(money: 0.12USD, time: 90ms)
    },
}
```

Shadow prices reflect current pricing, automatically routing to cheapest provider.

---

## Real-Time Resource Constraints

### Hard Deadlines

Some systems have **non-negotiable** time constraints:

```eclexia
resource time {
    budget: 10ms,  // MUST finish in 10ms
    shadow: compute_time_price(),
}

fn process_sensor_data(data: SensorData) -> Result<Control, String> {
    // If this exceeds 10ms, system fails
    let result = analyze_data(data) @requires(time: 8ms);
    Ok(compute_control(result))
}
```

Eclexia's static analysis **verifies** worst-case time bounds.

### Priority-Based Scheduling

Critical tasks get more budget:

```eclexia
fn control_loop() {
    resource time { budget: 100ms }

    // High-priority: Always runs
    let sensor_data = read_sensors() @requires(time: 5ms);
    let control = compute_control(sensor_data) @requires(time: 10ms);
    apply_control(control) @requires(time: 5ms);

    // Medium-priority: Runs if time permits
    adaptive diagnostics {
        run: {
            run_diagnostics() @requires(time: 30ms)
        },
        skip: {
            Ok(())  // No-op if no time
        },
    }

    // Low-priority: Runs if time permits
    adaptive logging {
        run: {
            log_telemetry() @requires(time: 20ms)
        },
        skip: {
            Ok(())
        },
    }
}
```

### Deadline Awareness

Compute **remaining time** dynamically:

```eclexia
fn main() {
    resource time {
        budget: 100ms,
        shadow: compute_time_price(),
    }

    let start = time.elapsed();

    loop {
        let remaining = time.remaining();
        if remaining < 10ms {
            break;  // Not enough time for another iteration
        }

        process_one_item() @requires(time: 8ms);
    }

    finalize() @requires(time: 5ms);
}
```

---

## Advanced Patterns

### Resource Pools

Share resources across tasks:

```eclexia
struct ResourcePool {
    energy_budget: Energy,
    time_budget: Time,
}

impl ResourcePool {
    fn allocate(&mut self, task: Task) -> Result<(), String> {
        if self.energy_budget >= task.energy_cost &&
           self.time_budget >= task.time_cost {
            self.energy_budget -= task.energy_cost;
            self.time_budget -= task.time_cost;
            Ok(())
        } else {
            Err("Insufficient resources")
        }
    }
}
```

### Resource Virtualization

Decouple logical and physical resources:

```eclexia
resource logical_cpu {
    budget: 100%,
    shadow: compute_cpu_price(),
}

fn physical_cores() -> Int {
    platform_cpu_count()
}

fn schedule_task(task: Task) {
    let logical_cost = task.compute_requirement();
    let physical_cost = logical_cost / physical_cores();

    task.run() @requires(logical_cpu: physical_cost)
}
```

### Probabilistic Budgets

Handle uncertainty with safety margins:

```eclexia
fn ml_inference(model: Model, input: Data) -> Result<Output, String> {
    // Worst-case: 100ms, average: 50ms, best-case: 20ms
    let safety_margin = 1.2;
    let expected_time = 50ms * safety_margin;  // 60ms

    resource time { budget: 100ms }

    if time.remaining() >= expected_time {
        model.predict(input) @requires(time: expected_time)
    } else {
        Err("Insufficient time budget")
    }
}
```

### Hierarchical Resource Management

Nested resource contexts:

```eclexia
fn main() {
    resource global_energy { budget: 10000J }

    for task in tasks {
        // Each task gets a slice of global budget
        resource task_energy {
            budget: 1000J,
            parent: global_energy,
        }

        process_task(task);

        // task_energy consumption deducted from global_energy
    }
}
```

---

## Performance and Profiling

### Measuring Resource Consumption

Built-in profiler:

```eclexia
use time::{Instant};

fn benchmark_algorithm() {
    resource energy { budget: 10000J }
    resource time { budget: 1000ms }

    let start = Instant::now();
    let energy_before = energy.remaining();

    expensive_algorithm();

    let elapsed = start.elapsed();
    let energy_used = energy_before - energy.remaining();

    print("Time: " + elapsed);
    print("Energy: " + energy_used);
}
```

### Shadow Price Analysis

Track how shadow prices evolve:

```eclexia
fn analyze_shadow_prices() {
    resource time { budget: 100ms, shadow: compute_time_price() }

    let mut prices = Vec::new();

    for i in 0..10 {
        prices.push(time.shadow_price);
        do_work() @requires(time: 8ms);
    }

    print("Shadow price progression:");
    for (i, price) in prices.iter().enumerate() {
        print("Iteration " + i + ": " + price);
    }
}
```

Output:
```
Shadow price progression:
Iteration 0: 0.01
Iteration 1: 0.09
Iteration 2: 0.25
Iteration 3: 0.49
Iteration 4: 0.81
Iteration 5: 1.21
Iteration 6: 1.69
Iteration 7: 2.25
Iteration 8: 2.89
Iteration 9: 3.61
```

Shadow price increases as budget depletes.

### Bottleneck Identification

Find resource hotspots:

```eclexia
fn profile_pipeline() {
    resource time { budget: 1000ms }
    resource memory { budget: 1000MB }

    let stages = [
        ("Load", load_data),
        ("Process", process_data),
        ("Analyze", analyze_data),
        ("Save", save_results),
    ];

    for (name, stage) in stages {
        let time_before = time.remaining();
        let mem_before = memory.remaining();

        stage();

        let time_used = time_before - time.remaining();
        let mem_used = mem_before - memory.remaining();

        print(name + " - Time: " + time_used + ", Memory: " + mem_used);
    }
}
```

Output:
```
Load - Time: 100ms, Memory: 200MB
Process - Time: 500ms, Memory: 400MB  ← Bottleneck
Analyze - Time: 200ms, Memory: 100MB
Save - Time: 50ms, Memory: 50MB
```

---

## Best Practices

### 1. Set Realistic Budgets

**Bad:**
```eclexia
resource time { budget: 1s }  // Way more than needed
expensive_operation() @requires(time: 10ms);  // Uses 1% of budget
```

**Good:**
```eclexia
resource time { budget: 50ms }  // Tight but feasible
expensive_operation() @requires(time: 10ms);  // Uses 20% of budget
```

Tight budgets provide better shadow price signals.

### 2. Annotate All Costs

**Bad:**
```eclexia
fn process() {
    work1();  // Unknown cost
    work2();  // Unknown cost
}
```

**Good:**
```eclexia
fn process() {
    work1() @requires(time: 10ms, energy: 50J);
    work2() @requires(time: 5ms, energy: 20J);
}
```

Explicit costs enable compile-time verification.

### 3. Provide Fallbacks

**Bad:**
```eclexia
adaptive compress {
    high_quality: { ... },  // Only option
}
```

If high_quality fails, entire program fails.

**Good:**
```eclexia
adaptive compress {
    high_quality: { ... },
    medium_quality: { ... },
    low_quality: { ... },
    no_compression: { Ok(data) },  // Always succeeds
}
```

Always have a fallback that can't fail.

### 4. Monitor Shadow Prices

**Bad:**
```eclexia
// Ignore shadow prices, just check remaining budget
if time.remaining() > 10ms {
    expensive_operation();
}
```

**Good:**
```eclexia
// Use shadow prices to guide decisions
if time.shadow_price < 5.0 {  // Still relatively cheap
    expensive_operation();
} else {
    cheaper_alternative();
}
```

Shadow prices provide early warning of scarcity.

### 5. Test Under Constrained Conditions

**Bad:**
```eclexia
// Only test with generous budgets
resource time { budget: 10s }  // Won't catch budget violations
```

**Good:**
```eclexia
#[test]
fn test_low_battery() {
    resource battery { budget: 100J }  // Simulate low battery
    assert!(process_data().is_ok());  // Must still succeed
}
```

Test with minimal budgets to find edge cases.

---

## Summary

You've learned to write **resource-aware programs** that:

✅ **Track multiple resources** (energy, time, memory, money, carbon)
✅ **Adapt to constraints** (choose algorithms based on availability)
✅ **Optimize for carbon** (defer work to low-carbon periods)
✅ **Conserve battery** (adapt mobile app behavior)
✅ **Minimize cloud costs** (select cheapest instances/regions)
✅ **Meet real-time deadlines** (verify time constraints)
✅ **Profile and optimize** (identify resource hotspots)

### Next Steps

**Tutorial 3: Advanced Type System**
Dive deep into dimensional analysis, type inference, generic programming, and implementing your own type-checked DSLs.

**Tutorial 4: Economics-as-Code**
Master shadow pricing theory, implement market equilibrium models, and use Eclexia for quantitative economics research.

### Practice Projects

1. **Carbon-Aware CI/CD**: Schedule builds when renewable energy is abundant
2. **Battery Saver App**: Adaptive video player that reduces quality when battery is low
3. **Multi-Cloud Scheduler**: Route tasks to cheapest cloud provider in real-time
4. **Real-Time Controller**: Control system with hard deadlines and graceful degradation
5. **Energy Dashboard**: Monitor and visualize resource consumption across services

---

**Total Words:** ~5,400

This tutorial equips you with practical patterns for building resource-aware applications. The next tutorial will explore Eclexia's advanced type system in depth.
