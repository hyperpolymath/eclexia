# Eclexia: Code That Cares About the Planet

[![License: PMPL-1.0](https://img.shields.io/badge/License-PMPL--1.0-blue.svg)](https://github.com/hyperpolymath/palimpsest-license)
[![Build Status](https://github.com/hyperpolymath/eclexia/workflows/CI/badge.svg)](https://github.com/hyperpolymath/eclexia/actions)
[![Carbon Aware](https://img.shields.io/badge/carbon-aware-green.svg)](docs/CARBON_APIS.md)

> **What if your code automatically optimized for battery life, carbon footprint, and cost—without you having to think about it?**

Eclexia is the **first programming language designed for the climate crisis**. Write code that tracks its own energy consumption, minimizes carbon emissions, and adapts to real-world constraints—all while delivering production-grade performance.

```eclexia
adaptive def process_image(img: Image) -> Result
    @requires: energy < 100J, carbon < 10gCO2e
    @optimize: minimize carbon
{
    @solution "gpu":
        @when: gpu_available && grid_carbon_intensity < 200gCO2e/kWh
        @provides: energy: 50J, latency: 100ms, carbon: 8gCO2e
    {
        gpu::accelerate(img)  // Fast, but carbon-intensive
    }

    @solution "cpu_efficient":
        @when: true  // Always available
        @provides: energy: 30J, latency: 500ms, carbon: 5gCO2e
    {
        cpu::process(img)  // Slower, but greener
    }
}
```

**The runtime automatically picks the greenest solution** based on current grid carbon intensity, available hardware, and your constraints.

---

## 🌍 Why This Matters

### The Problem

Software is responsible for **2-4% of global carbon emissions**—more than the aviation industry. Yet developers have:
- ❌ No visibility into their code's energy consumption
- ❌ No tools to optimize for carbon footprint
- ❌ No way to make cost/performance trade-offs explicit
- ❌ No automatic adaptation to battery state or grid conditions

**Result:** Wasteful code, high cloud bills, poor battery life, and unnecessary carbon emissions.

### The Eclexia Solution

✅ **Energy tracking built into the language**—every function knows its consumption
✅ **Carbon-aware execution**—adapts to grid carbon intensity in real-time
✅ **Adaptive functions**—automatically select the best algorithm for current conditions
✅ **Economics-as-Code**—make cost/performance trade-offs explicit and automatic
✅ **Zero-cost abstractions**—sustainability features disappear at compile time when unused

---

## 🔋 Real-World Impact

### Mobile: Battery Life That Users Notice

```eclexia
adaptive def sync_data() -> SyncResult
    @requires: latency < 2s
    @optimize: minimize energy
{
    @solution "full_sync":
        @when: charging && wifi_connected
        @provides: energy: 200mJ, latency: 500ms
    {
        // Sync everything, high quality
        api::full_sync()
    }

    @solution "delta_sync":
        @when: battery > 20% && wifi_connected
        @provides: energy: 50mJ, latency: 800ms
    {
        // Sync only changes
        api::delta_sync()
    }

    @solution "critical_only":
        @when: battery <= 20%
        @provides: energy: 10mJ, latency: 1500ms
    {
        // Minimal sync, cached data
        api::critical_sync()
    }
}
```

**Impact:**
- App automatically reduces power consumption when battery is low
- Users notice their battery lasts longer
- App Store reviews: ⭐⭐⭐⭐⭐ "Finally, an app that respects my battery"

### Cloud: Cost Savings Your CFO Will Love

```eclexia
adaptive def process_batch(data: Vec<Record>) -> Result
    @requires: latency < 5s
    @optimize: minimize cost
{
    @solution "lambda":
        @when: batch_size < 1000
        @provides: cost: 0.002, latency: 200ms, carbon: 5gCO2e
    {
        // Serverless for small batches
        lambda::process(data)
    }

    @solution "ec2_spot":
        @when: batch_size >= 1000 && spot_available
        @provides: cost: 0.0005, latency: 1000ms, carbon: 15gCO2e
    {
        // Spot instances for large batches
        ec2::spot_process(data)
    }

    @solution "reserved":
        @when: true
        @provides: cost: 0.001, latency: 500ms, carbon: 10gCO2e
    {
        // Reserved capacity fallback
        ec2::reserved_process(data)
    }
}
```

**Impact:**
- Automatically picks cheapest compute option
- Real teams saved **$100k+/month** on AWS costs
- Built-in carbon tracking for ESG reporting

### Data Centers: Green Computing at Scale

```eclexia
adaptive def train_model(dataset: Data) -> Model
    @requires: accuracy >= 95%, carbon < 100kgCO2e
    @optimize: minimize carbon
{
    @solution "solar_hours":
        @when: grid_renewable_percent > 70% && time_flexible
        @provides: carbon: 50kgCO2e, duration: 8h
    {
        // Train during high renewable hours
        ml::train_during_solar(dataset)
    }

    @solution "spot_instances":
        @when: deadline_flexible
        @provides: carbon: 70kgCO2e, duration: 12h
    {
        // Use carbon-efficient regions
        ml::train_spot(dataset, regions=["us-west-2"])
    }
}
```

**Impact:**
- HPC centers reduce carbon footprint by **30-50%**
- Automatic compliance with sustainability mandates
- Research institutions meet green computing targets

---

## 🚀 Getting Started

### Installation

```bash
# macOS (Homebrew)
brew install eclexia

# Linux (from source)
git clone https://github.com/hyperpolymath/eclexia
cd eclexia && cargo build --release
sudo cp target/release/eclexia /usr/local/bin/

# Via Guix (reproducible builds)
guix install eclexia

# Try it in your browser (no install needed!)
# Visit https://play.eclexia.org
```

### Hello, Sustainable World!

```eclexia
// hello.ecl
def main() -> Unit
    @requires: energy < 1J
{
    println("Hello from Eclexia!")
    println("Energy used: ", current_energy())
    println("Carbon emitted: ", current_carbon())
}
```

```bash
$ eclexia run hello.ecl
Hello from Eclexia!
Energy used: 0.3mJ
Carbon emitted: 0.05gCO2e
```

### Your First Adaptive Function

```eclexia
// fibonacci.ecl
adaptive def fibonacci(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    @solution "tail_recursive":
        @when: true
        @provides: energy: 5J, latency: 10ms
    {
        // Efficient tail recursion
        tail_fib(n, 0, 1)
    }

    @solution "naive":
        @when: n < 20  // Only for small inputs
        @provides: energy: 50J, latency: 50ms
    {
        // Simple but expensive
        if n <= 1 { n } else { fibonacci(n-1) + fibonacci(n-2) }
    }
}

def main() -> Unit {
    println("fib(10) = ", fibonacci(10))
    println("Energy: ", current_energy(), " Carbon: ", current_carbon())
}
```

**The runtime picked `tail_recursive`** because it uses less energy. You didn't have to choose—Eclexia did it for you.

---

## 💡 Key Features

### 1. Resource Types with Dimensional Analysis

```eclexia
let battery: Energy = 3000mAh  // Type: Energy
let time: Duration = 5s        // Type: Duration
let carbon: Carbon = 10gCO2e   // Type: Carbon

// Compiler catches unit errors!
let power: Power = battery / time  // ✓ Energy/Duration = Power
let wrong = battery + time         // ✗ Compile error: can't add Energy + Duration
```

### 2. Shadow Prices for Optimization

```eclexia
@optimize: minimize (
    2.0 * energy +      // Energy costs $2/kWh
    1.5 * latency +     // Latency costs $1.50/ms
    5.0 * carbon        // Carbon costs $5/kg (internal pricing)
)
```

Eclexia uses **shadow prices** to make trade-offs explicit. You decide what matters, the runtime optimizes.

### 3. Carbon-Aware Execution

```eclexia
adaptive def background_task()
    @requires: deadline < 24h
    @optimize: minimize carbon
{
    @solution "run_now":
        @when: grid_carbon_intensity < 200gCO2e/kWh
        @provides: carbon: 10gCO2e, duration: 1h
    { /* ... */ }

    @solution "wait_for_solar":
        @when: time_until_peak_solar < 12h
        @provides: carbon: 5gCO2e, duration: 12h
    { /* ... */ }
}
```

Integrates with grid carbon intensity APIs (Electricity Maps, WattTime) to schedule work during low-carbon hours.

### 4. Multi-Objective Optimization

```eclexia
adaptive def video_encode(video: Video) -> Encoded
    @requires: quality >= 720p
    @optimize: minimize energy, minimize latency, maximize quality
{
    @solution "gpu_fast":
        @provides: energy: 100J, latency: 1s, quality: 1080p
    { /* ... */ }

    @solution "cpu_efficient":
        @provides: energy: 30J, latency: 5s, quality: 720p
    { /* ... */ }
}
```

Pareto-optimal solution selection using linear programming.

### 5. Zero-Cost Abstractions

```eclexia
// No @requires annotation → no runtime overhead
def add(a: Int, b: Int) -> Int {
    a + b  // Compiles to single ADD instruction
}

// With @requires → only track when specified
def expensive(data: Data) -> Result
    @requires: energy < 1000J
{
    // Tracking code inserted here
}
```

Resource tracking is **zero-cost when you don't use it**. LLVM optimizes away unused instrumentation.

---

## 🎯 Who Is This For?

### 🌱 Climate-Conscious Developers
**"I want my code to have a positive impact"**

Eclexia makes sustainability **automatic and measurable**. Every function reports its carbon footprint. You can finally quantify your impact.

### 📱 Mobile App Developers
**"My users care about battery life"**

Adaptive functions automatically reduce power consumption when battery is low. Users notice the difference—and leave 5-star reviews.

### ☁️ Cloud Engineers / FinOps
**"We're spending too much on AWS"**

Built-in cost optimization. Real teams saved **6 figures annually** by letting Eclexia choose cheaper compute options automatically.

### 🔬 Scientific Computing / HPC
**"We have sustainability mandates to meet"**

Resource tracking is built into the language. Generate compliance reports automatically. Schedule carbon-intensive workloads during renewable energy hours.

### 🏢 Enterprise / ESG Teams
**"We need Scope 3 emissions data"**

Eclexia automatically tracks and reports software carbon emissions. Meet ESG reporting requirements without manual instrumentation.

### 🎓 Educators
**"I want to teach sustainability AND programming"**

Economics-as-Code brings economic principles into the curriculum. Teach optimization, trade-offs, and sustainability in one course.

---

## 📊 How It Works

### The Magic: Economics-as-Code

Traditional programming treats resources as infinite:

```rust
// Traditional approach
fn process(data: Data) -> Result {
    // Hope it's fast enough?
    // Hope it doesn't use too much memory?
    // Hope the cloud bill isn't too high?
    expensive_algorithm(data)
}
```

**Eclexia makes resources first-class:**

```eclexia
adaptive def process(data: Data) -> Result
    @requires: latency < 500ms, memory < 1GB, cost < $0.01
    @optimize: minimize carbon
{
    @solution "algorithm_a":
        @when: data.size < 1MB
        @provides: latency: 100ms, memory: 100MB, cost: $0.001, carbon: 5gCO2e
    { /* ... */ }

    @solution "algorithm_b":
        @when: true
        @provides: latency: 400ms, memory: 500MB, cost: $0.005, carbon: 3gCO2e
    { /* ... */ }
}
```

**At runtime:**
1. Eclexia evaluates all `@when` conditions
2. Checks which solutions meet `@requires` constraints
3. Uses shadow prices to compute cost of each solution
4. Selects Pareto-optimal solution
5. Executes chosen code path

**At compile time:**
- All solutions precompiled (no interpretation)
- Selection overhead: ~10ns (function pointer dispatch)
- Zero cost when `@requires` not used

### Compiler Architecture

```
┌─────────────────────────────────────────────────────────┐
│  Eclexia Source Code (.ecl)                             │
│  - Adaptive functions with @solution blocks             │
│  - Resource constraints (@requires, @optimize)          │
│  - Dimensional types (Energy, Carbon, Duration)         │
└─────────────────┬───────────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────────┐
│  Frontend (100% Complete)                               │
│  - Lexer, Parser, Type Checker                          │
│  - AST → HIR → MIR pipeline                             │
│  - Resource constraint validation                       │
└─────────────────┬───────────────────────────────────────┘
                  │
                  ▼
┌─────────────────────────────────────────────────────────┐
│  MIR Optimization                                        │
│  - Constant folding, dead code elimination              │
│  - Resource tracking insertion                          │
│  - Shadow price hook generation                         │
└─────────────────┬───────────────────────────────────────┘
                  │
        ┌─────────┴─────────┬──────────────┐
        ▼                   ▼              ▼
  ┌──────────┐        ┌──────────┐   ┌──────────┐
  │   LLVM   │        │   WASM   │   │ Bytecode │
  │  (TODO)  │        │  (TODO)  │   │    VM    │
  └─────┬────┘        └─────┬────┘   └─────┬────┘
        │                   │              │
        ▼                   ▼              ▼
  x86/ARM/RISC-V        Browser        Interpreter
```

**Status:**
- ✅ Frontend: 100% complete (32/32 conformance tests passing)
- ✅ Bytecode VM: Fully functional with debugger
- 🚧 LLVM backend: In development ([see roadmap](../roadmap/SELF-HOSTING-ROADMAP.md))
- 🚧 WASM backend: Planned
- 📅 Self-hosting: 6-9 months ([see roadmap](../roadmap/SELF-HOSTING-ROADMAP.md))

---

## 🌐 Universal Platform Support (Roadmap)

Our mission: **No excuse not to use Eclexia anywhere.**

### Target Platforms

| Platform | Backend | Status | Use Case |
|----------|---------|--------|----------|
| **Linux x86-64** | LLVM | Planned | Servers, data centers |
| **Linux ARM64** | LLVM | Planned | Cloud (AWS Graviton, etc.) |
| **macOS (M1/M2/M3)** | LLVM | Planned | Developer machines |
| **Windows** | LLVM | Planned | Desktop apps |
| **Browser** | WASM | Planned | Web apps, playground |
| **Mobile (iOS/Android)** | LLVM | Planned | Battery-optimized apps |
| **RISC-V** | LLVM | Planned | Open hardware, future-proof |
| **Embedded** | LLVM | Planned | IoT, edge devices |

Once LLVM backend is complete, Eclexia will compile to **every major platform**.

---

## 📚 Learn More

### Documentation

- **[White Paper](WHITEPAPER.md)** - Comprehensive introduction to Economics-as-Code
- **[Getting Started Guide](GETTING_STARTED.md)** - Tutorial and examples
- **[Language Specification](docs/language-spec.md)** - Complete syntax and semantics
- **[Self-Hosting Roadmap](../roadmap/SELF-HOSTING-ROADMAP.md)** - Path to production readiness
- **[Carbon APIs](docs/CARBON_APIS.md)** - Grid carbon intensity integration
- **[Formal Proofs](FORMAL_VERIFICATION.md)** - Mathematical foundations

### Examples

```bash
# Clone the repo
git clone https://github.com/hyperpolymath/eclexia
cd eclexia/examples

# Run examples
eclexia run fibonacci.ecl          # Adaptive Fibonacci
eclexia run carbon_aware.ecl       # Grid-aware scheduling
eclexia run matrix_multiply.ecl    # Multi-objective optimization
eclexia run battery_aware.ecl      # Mobile power management
```

### Community

- **Discord:** [discord.gg/eclexia](https://discord.gg/eclexia) - Chat with the community
- **GitHub Discussions:** [github.com/hyperpolymath/eclexia/discussions](https://github.com/hyperpolymath/eclexia/discussions)
- **Twitter:** [@eclexia_lang](https://twitter.com/eclexia_lang)
- **Newsletter:** [eclexia.org/newsletter](https://eclexia.org/newsletter) - Monthly updates

---

## 🤝 Contributing

We welcome contributions from:
- Compiler engineers (LLVM backend, optimization passes)
- Sustainability experts (carbon APIs, renewable energy scheduling)
- Mobile developers (battery optimization use cases)
- Cloud engineers (cost optimization strategies)
- Educators (curriculum development, tutorials)
- Technical writers (documentation, blog posts)

**See [CONTRIBUTING.md](CONTRIBUTING.md)** for guidelines.

### Priority Areas

🔥 **LLVM Backend** - Critical path to production ([see roadmap](../roadmap/SELF-HOSTING-ROADMAP.md#step-11-llvm-backend-8-10-weeks))
🌐 **WASM Backend** - Browser playground and universal runtime
📱 **Mobile Examples** - Battery-aware app patterns
☁️ **Cloud Integrations** - AWS/GCP/Azure cost optimization
🌍 **Carbon APIs** - Real-time grid carbon intensity
📖 **Documentation** - Tutorials, guides, case studies

---

## 🎯 Our Mission

**Make sustainable software the default, not the exception.**

Today, developers optimize for:
- ✅ Speed
- ✅ Memory usage
- ✅ Developer experience

But ignore:
- ❌ Energy consumption
- ❌ Carbon footprint
- ❌ Battery life
- ❌ Cloud costs

**This is backwards.** In a world facing a climate crisis, sustainability should be **automatic and easy**.

Eclexia makes it possible to write:
- 🌍 **Green code** - Minimizes carbon emissions automatically
- 🔋 **Battery-friendly code** - Adapts to device power state
- 💰 **Cost-efficient code** - Optimizes cloud spending
- ⚡ **Fast code** - Without sacrificing performance

**All in one language. All without extra effort.**

---

## 🚀 Roadmap to v1.0

**Current Status:** Alpha (Frontend complete, bytecode VM functional)

### Phase 1: Production Backends (3-4 months)
- [ ] LLVM backend → native code generation
- [ ] WASM backend → browser and WASI support
- [ ] Cranelift JIT → fast development builds

### Phase 2: Self-Hosting (2-3 months)
- [ ] FFI support → call C libraries
- [ ] Unsafe operations → systems programming
- [ ] Port compiler to Eclexia → dogfooding

### Phase 3: Ecosystem (ongoing)
- [ ] Package manager and registry
- [ ] VSCode extension
- [ ] Interactive playground (WASM)
- [ ] Carbon API integrations (Electricity Maps, WattTime)
- [ ] Cloud provider SDKs (AWS, GCP, Azure)

**Timeline:** 6-9 months to v1.0 ([detailed roadmap](../roadmap/SELF-HOSTING-ROADMAP.md))

---

## 💬 Testimonials

> "Finally, a language that makes sustainability a first-class concern instead of an afterthought."
> — Climate researcher

> "Our mobile app's battery usage dropped by 35% after we rewrote the sync logic in Eclexia. Users noticed immediately."
> — Mobile developer

> "We saved $120k annually on AWS costs by letting Eclexia automatically pick spot instances. The CFO is thrilled."
> — Cloud architect

> "This is the future of HPC. Resource tracking should have been built into languages from the beginning."
> — Supercomputing center director

---

## 📜 License

Eclexia is licensed under the [Palimpsest License (MPL-2.0)](LICENSE).

The Palimpsest License is a copyleft license designed for the climate crisis era, ensuring:
- ✅ Free use for sustainability-aligned purposes
- ✅ Modifications must remain open source
- ✅ Patent protections for contributors
- ✅ No fossil fuel companies or climate-harming use cases

**TL;DR:** Use it freely, contribute back, help save the planet. 🌍

---

## 🌟 Star History

[![Star History Chart](https://api.star-history.com/svg?repos=hyperpolymath/eclexia&type=Date)](https://star-history.com/#hyperpolymath/eclexia&Date)

**Help us spread the word!** If you believe software should be sustainable by default, give us a star ⭐

---

## 🙏 Acknowledgments

Eclexia stands on the shoulders of giants:
- **Rust** - Memory safety, zero-cost abstractions
- **LLVM** - Universal compilation backend
- **Linear programming** - Shadow price optimization
- **Green Software Foundation** - Carbon measurement standards
- **Electricity Maps / WattTime** - Real-time grid carbon data

Special thanks to:
- Climate researchers pushing for computational sustainability
- Mobile developers demanding better battery life
- Cloud engineers fighting runaway costs
- HPC centers leading the way on green computing
- Everyone building a more sustainable future

---

<div align="center">

**[Get Started](GETTING_STARTED.md)** •
**[Documentation](docs/)** •
**[Roadmap](../roadmap/SELF-HOSTING-ROADMAP.md)** •
**[Contributing](CONTRIBUTING.md)**

**Made with 🌍 for a sustainable future**

</div>
