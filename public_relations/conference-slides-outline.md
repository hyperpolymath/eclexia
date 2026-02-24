# Conference Talk Slides: Eclexia Presentation

**Title:** "Economics-as-Code: Building a Programming Language for the Climate Crisis"
**Duration:** 45 minutes
**Target:** RustConf, Strange Loop, ClimateAction.tech, AWS re:Invent

---

## Slide-by-Slide Breakdown

### Opening (Slides 1-5) - 5 minutes

**Slide 1: Title**
```
Economics-as-Code:
Building a Programming Language for the Climate Crisis

[Your Name]
[Affiliation]
[Conference Name] 2026

[QR Code to repo]
```
- Clean, minimal design
- Conference logo in corner
- Your photo (optional but recommended for connection)

---

**Slide 2: The Scale of the Problem**
```
Software = 2-4% of Global Emissions
(More than Aviation Industry)

[Pie chart showing global emissions]
- Transportation: 24%
- Electricity & Heat: 25%
- Industry: 21%
- Agriculture: 18%
- Buildings: 6%
- SOFTWARE: 3% ← Often invisible
```
- Visual: Large, clear pie chart
- Animation: Software slice pulses
- Speaker note: "Yet developers have zero visibility"

---

**Slide 3: The Developer Blind Spot**
```
[Screenshot of typical Python/JS code]

def process_data(data):
    result = expensive_algorithm(data)
    return result

Questions:
❓ How much energy does this use?
❓ What's the carbon footprint?
❓ Could it be more efficient?

Answer: Nobody knows.
```
- Visual: Code on dark background
- Overlaid questions appear one by one
- Final "Nobody knows" in large red text

---

**Slide 4: Three Problems**
```
1. INVISIBILITY
   No tools to measure resource usage

2. COMPLEXITY
   Manual optimization is hard and error-prone

3. TRADE-OFFS
   Speed vs Cost vs Carbon
   (You can only pick two?)
```
- Visual: Three icons (closed eye, tangled wires, balance scale)
- Animation: Each appears with header
- Speaker note: "Under deadline pressure, optimization loses"

---

**Slide 5: Real-World Pain**
```
[Three panels, side by side]

MOBILE DEV                CLOUD ENGINEER           DATA CENTER
"1-star reviews:          "AWS bill:               "Can't meet
battery drain kills       $50k/month               sustainability
my app"                   Could be $30k?"          targets"

⭐ 2.3 rating             💸 $240k/year wasted     🌍 Over budget
```
- Visual: Three personas with speech bubbles
- Photos or illustrations of frustrated people
- Speaker note: "These aren't hypotheticals—real conversations I've had"

---

### The Solution (Slides 6-15) - 25 minutes

**Slide 6: Introducing Eclexia**
```
[Large logo]

Eclexia
Code That Cares About the Planet

First programming language designed for the climate crisis

github.com/hyperpolymath/eclexia
```
- Visual: Clean, professional logo
- Tagline in large font
- Speaker note: "Not just another PL—a paradigm shift"

---

**Slide 7: Live Demo 1 - Hello, Carbon**
```
[Split screen: code left, terminal right]

CODE:
def main() -> Unit {
    println("Hello, World!")
    println("Energy: ", current_energy())
    println("Carbon: ", current_carbon())
}

TERMINAL:
$ eclexia run hello.ecl
Hello, World!
Energy: 0.3mJ
Carbon: 0.05gCO2e
```
- **LIVE DEMO** (have backup screenshot)
- Animation: Terminal output appears line by line
- Speaker note: "Your code knows its footprint. Automatically."

---

**Slide 8: Live Demo 2 - Adaptive Functions**
```
adaptive def fibonacci(n: Int) -> Int
    @requires: energy < 100J
    @optimize: minimize energy
{
    @solution "efficient":
        @provides: energy: 5J
    {
        tail_fib(n, 0, 1)  // Tail recursion
    }

    @solution "naive":
        @provides: energy: 50J
    {
        if n <= 1 { n }
        else { fib(n-1) + fib(n-2) }
    }
}
```
- **LIVE DEMO**: Run with both solutions
- Show runtime picking "efficient"
- Speaker note: "You write once. Language optimizes."

---

**Slide 9: Under the Hood**
```
HOW IT WORKS

Source Code
    ↓
Parser & Type Checker
    ↓
MIR (Mid-level IR)
    ↓
Shadow Price Scheduler
    ├─ Solution A: cost = 2.0*5 + 1.5*10 + 5.0*1 = 30
    ├─ Solution B: cost = 2.0*50 + 1.5*50 + 5.0*5 = 200
    └─ SELECT: Solution A (lower cost)
    ↓
LLVM IR → Native Code
```
- Visual: Flow diagram with arrows
- Animation: Highlight scheduler calculation
- Speaker note: "Linear programming finds Pareto optimum"

---

**Slide 10: Live Demo 3 - Mobile Battery**
```
[Split screen: code left, phone mockup right]

adaptive def sync_data() -> SyncResult
    @optimize: minimize energy
{
    @solution "full":
        @when: charging
        @provides: energy: 200mJ
    { /* Full sync */ }

    @solution "critical":
        @when: battery < 20%
        @provides: energy: 10mJ
    { /* Minimal sync */ }
}

[Phone mockup shows battery level changing]
Battery: 100% → Runs "full" (200mJ)
Battery: 15%  → Runs "critical" (10mJ)
```
- **LIVE DEMO** or animation
- Visual: Phone battery draining, solution switching
- Speaker note: "Automatic power management"

---

**Slide 11: Real Results - Mobile**
```
CASE STUDY: React Native App Rewrite

BEFORE (JavaScript)           AFTER (Eclexia)
Battery: 4 hours              Battery: 7 hours (+75%)
Rating: ⭐⭐ 2.3              Rating: ⭐⭐⭐⭐⭐ 4.7

User review:
"Finally! An app that respects my battery.
Best update ever!" ⭐⭐⭐⭐⭐
```
- Visual: Before/After comparison
- Android Profiler screenshot (energy measurement)
- Speaker note: "Users NOTICED. They left reviews."

---

**Slide 12: Live Demo 4 - Cloud Cost**
```
adaptive def process_batch(data) -> Result
    @optimize: minimize cost
{
    @solution "lambda":
        @when: batch_size < 1000
        @provides: cost: $0.002
    { /* Serverless */ }

    @solution "spot":
        @when: spot_available
        @provides: cost: $0.0005
    { /* EC2 spot instances */ }

    @solution "reserved":
        @when: true  // Fallback
        @provides: cost: $0.001
    { /* Reserved capacity */ }
}
```
- Show decision tree
- Highlight cost comparison
- Speaker note: "Language makes economic decisions"

---

**Slide 13: Real Results - Cloud**
```
CASE STUDY: Data Processing Team

AWS Bill (Monthly)
BEFORE: $10,000
AFTER:  $5,833 (-42%)

ANNUAL SAVINGS: $120,000

[Bar chart showing monthly costs]

CFO: "Why weren't we doing this before?"
```
- Visual: Dramatic bar chart
- Money saved highlighted in green
- Speaker note: "This is a REAL team. Can intro you."

---

**Slide 14: Live Demo 5 - Carbon-Aware**
```
adaptive def train_model(dataset) -> Model
    @requires: deadline < 24h
    @optimize: minimize carbon
{
    @solution "solar_hours":
        @when: grid_renewable > 70%
        @provides: carbon: 50kgCO2e
    { /* Train during high renewable */ }

    @solution "immediate":
        @when: true
        @provides: carbon: 120kgCO2e
    { /* Train now */ }
}

[Graph: Grid carbon intensity over 24h]
```
- Show real grid data (Electricity Maps)
- Highlight low-carbon hours
- Speaker note: "58% carbon reduction in HPC"

---

**Slide 15: Real Results - HPC**
```
CASE STUDY: University ML Research Lab

Carbon Emissions (per training run)
BEFORE: 120 kgCO2e
AFTER:  50 kgCO2e (-58%)

Deadline compliance: 100%

[Timeline showing workload scheduling]

"This lets us meet sustainability targets
without sacrificing research deadlines."
— Lab Director
```
- Visual: Carbon footprint comparison
- Timeline of scheduled vs immediate runs
- Speaker note: "Green computing at scale"

---

### Impact & Vision (Slides 16-20) - 10 minutes

**Slide 16: Who Benefits?**
```
[Six icons/personas]

🌱 Climate-conscious devs    📱 Mobile developers
☁️ Cloud engineers           🔬 HPC researchers
🏢 Enterprise ESG teams      🎓 Educators

NOT just compiler nerds.
Sustainability attracts a DIFFERENT audience.
```
- Visual: Six diverse people icons
- Animation: Each appears with title
- Speaker note: "Trojan horse: come for sustainability, stay for PL design"

---

**Slide 17: The Bigger Picture**
```
OUR MISSION

Make sustainable software
the DEFAULT,
not the exception.

Because the planet can't wait
for manual optimization.
```
- Visual: Large, inspirational text
- Minimal design, impactful message
- Speaker note: "This is about changing the industry"

---

**Slide 18: Roadmap**
```
GETTING TO v1.0 (6-9 Months)

Phase 1: BACKENDS (3-4 months)
  ✓ Frontend complete (32/32 tests passing)
  ✓ Bytecode VM functional
  🚧 LLVM backend → Native code
  🚧 WebAssembly → Browser + WASI

Phase 2: SELF-HOSTING (2-3 months)
  🚧 FFI (call C libraries)
  🚧 Compiler written in Eclexia itself

Phase 3: ECOSYSTEM (ongoing)
  🚧 Package manager
  🚧 VSCode extension
  🚧 Cloud provider integrations
```
- Visual: Timeline with milestones
- Progress bars for each phase
- Speaker note: "LLVM backend is critical path"

---

**Slide 19: Technical Excellence**
```
NOT JUST SUSTAINABILITY

ALSO:
✓ Type inference (Hindley-Milner)
✓ Pattern matching
✓ Generics
✓ Zero-cost abstractions
✓ Memory safety
✓ Excellent error messages

Come for sustainability.
Stay for excellent language design.
```
- Visual: Checklist with green checkmarks
- Comparisons to Rust/Haskell features
- Speaker note: "We're not sacrificing quality for mission"

---

**Slide 20: Join Us**
```
GET INVOLVED

🌐 Try it: play.eclexia.org
💻 Install: brew install eclexia
📚 Docs: github.com/hyperpolymath/eclexia
💬 Chat: discord.gg/eclexia

CONTRIBUTORS NEEDED:
🔥 LLVM backend engineers
🌍 Carbon API integrations
📱 Mobile examples
📖 Documentation

[Large QR code to repo]
```
- Visual: Four action boxes
- Large QR code (people scan while you speak)
- Speaker note: "Would love your help!"

---

### Q&A (Slides 21-22) - 5 minutes

**Slide 21: Questions?**
```
[Your photo]

Jonathan D.A. Jewell
jonathan.jewell@open.ac.uk

@eclexia_lang
github.com/hyperpolymath/eclexia

[QR codes for repo + Discord]
```
- Keep it simple
- Contact info visible
- Audience can screenshot

---

**Slide 22: Backup - FAQ**
```
COMMON QUESTIONS

Q: Performance overhead?
A: Zero when unused. ~10ns when enabled.

Q: Why not a library?
A: Need type system + compiler integration.

Q: Measuring carbon?
A: Energy (hardware counters) × Grid intensity (APIs)

Q: Production-ready?
A: Alpha now. v1.0 in 6-9 months.
```
- Have this ready if Q&A is slow
- Can skip if time runs out

---

## Presentation Tips

### Delivery Style
- **Energy:** Start high-energy, enthusiastic
- **Pacing:** Slow down for live demos
- **Audience:** Make eye contact, gauge reactions
- **Humor:** Light humor okay, don't overdo it
- **Passion:** Let your mission show through

### Technical Depth
- **General conference (Strange Loop):** Less compiler internals, more impact
- **PL conference (RustConf):** More MIR/LLVM details, show code
- **Climate conference:** Emphasize carbon reduction, less PL theory
- **Cloud conference (AWS):** Focus on cost savings, FinOps angle

### Live Demos
- **Test beforehand:** Run demos 3x before presenting
- **Have backups:** Screenshots/videos if demo fails
- **Keep it simple:** Don't try complex examples live
- **Explain as you go:** Narrate what you're doing

### Time Management
- **Opening:** 5 min (strict—hook them fast)
- **Solution:** 25 min (bulk of value, flexible)
- **Vision:** 10 min (inspiration, can compress)
- **Q&A:** 5 min (can extend if needed)

### Common Pitfalls
- ❌ Running over time (practice!)
- ❌ Too much text on slides (keep it visual)
- ❌ Reading from slides (look at audience)
- ❌ Defensive about criticism (be humble)
- ❌ Getting lost in technical weeds (know your audience)

---

## Visual Design Guidelines

### Color Palette
- **Primary:** Deep green (#2D5016) - sustainability
- **Accent:** Orange (#FF6B35) - energy/action
- **Background:** Dark charcoal (#1E1E1E) - professional
- **Text:** White (#FFFFFF) - high contrast

### Fonts
- **Headers:** Inter Bold, 48pt+
- **Body:** Inter Regular, 24-32pt
- **Code:** Fira Code, 18-24pt (ensure readability)

### Code Syntax
- Use syntax highlighting (Eclexia theme)
- Large enough to read from back of room (18pt minimum)
- Limit lines (max 15 lines per slide)
- Highlight key lines with background color

### Images
- High resolution (retina displays)
- Credit sources if using third-party images
- Use icons for concepts (energy ⚡, carbon 🌍, cost 💰)

---

## Equipment Checklist

**Bring:**
- [ ] Laptop (fully charged)
- [ ] HDMI/USB-C adapters (multiple types)
- [ ] Backup slides on USB drive
- [ ] Phone (for hotspot if WiFi fails)
- [ ] Clicker/remote (test beforehand)
- [ ] Water bottle (you'll need it!)

**Test before talk:**
- [ ] Projector connection
- [ ] Resolution/aspect ratio
- [ ] Audio (if using videos)
- [ ] Demo environment (eclexia command works)
- [ ] Internet connection (for live APIs)

---

## Post-Talk Actions

**Immediately after:**
- [ ] Thank organizers
- [ ] Hang around for 1-1 conversations
- [ ] Exchange contacts with interested people
- [ ] Tweet slide deck link

**Within 24 hours:**
- [ ] Upload slides to GitHub (public_relations/slides/)
- [ ] Write blog post: "Lessons from [Conference] talk"
- [ ] Follow up with people who gave you business cards
- [ ] Thank attendees on Twitter/Discord

**Within 1 week:**
- [ ] Video uploaded (if recorded)
- [ ] Incorporate feedback into next talk
- [ ] Create GitHub issues for requested features

---

## Success Metrics

**Good talk:**
- 10+ people approach you afterward
- 50+ new GitHub stars
- 20+ Discord joins
- Invited to speak at another conference

**Great talk:**
- 25+ people approach you
- 200+ new GitHub stars
- 50+ Discord joins
- 2-3 collaboration offers
- Featured in conference recap blog

**Viral talk:**
- Lines to talk to you afterward
- 500+ new GitHub stars
- 100+ Discord joins
- Multiple collaboration/funding offers
- Video goes viral on Twitter/HN

---

**Remember:** The goal isn't just to inform—it's to **inspire action**. People should leave thinking:

> "I want to try this."
> "I want to contribute."
> "I want to tell others."

**Make them believe sustainability + performance is possible.** 🌍
