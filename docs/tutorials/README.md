# Eclexia Tutorials

Comprehensive tutorial series for learning Eclexia, from beginner to expert level.

---

## Learning Path

### 1. [Getting Started with Eclexia](01-getting-started.md)

**Level:** Beginner
**Duration:** 2-3 hours
**Prerequisites:** Basic programming experience

Learn the fundamentals of Eclexia:
- Installation and setup
- Basic syntax and types
- Dimensional types for physical units
- Functions and control flow
- Data structures (arrays, vectors, hash maps)
- Error handling with Option and Result
- Introduction to resources and budgets

**Topics Covered:**
- Hello World with resource tracking
- Primitive and dimensional types
- If expressions and pattern matching
- Loops and iteration
- Working with the standard library
- Resource declaration and tracking

---

### 2. [Resource-Aware Programming](02-resource-aware-programming.md)

**Level:** Intermediate
**Duration:** 3-4 hours
**Prerequisites:** Getting Started tutorial

Master resource-aware programming patterns:
- Multi-resource management
- Adaptive execution for graceful degradation
- Carbon-aware scheduling
- Battery-conscious mobile applications
- Cost-optimized cloud services
- Real-time resource constraints

**Topics Covered:**
- Shadow prices and resource tradeoffs
- Adaptive blocks with multiple implementations
- Carbon-intensity APIs and geographic load shifting
- Battery-aware UI rendering and background tasks
- Spot instance bidding and multi-cloud optimization
- Priority-based scheduling with hard deadlines

**Practice Projects:**
- Carbon-aware CI/CD pipeline
- Battery saver video player
- Multi-cloud task scheduler
- Real-time control system with degradation

---

### 3. [Advanced Type System](03-advanced-type-system.md)

**Level:** Advanced
**Duration:** 4-5 hours
**Prerequisites:** Resource-aware programming, basic type theory

Deep dive into Eclexia's sophisticated type system:
- Dimensional analysis with phantom types
- Hindley-Milner type inference
- Generic programming and higher-kinded types
- Trait system and ad-hoc polymorphism
- Subtyping, variance, and type safety
- Type-level computation
- Effect system for tracking side effects

**Topics Covered:**
- Dimension algebra and type rules
- Bidirectional type checking
- Bounded generics and associated types
- Trait inheritance and blanket implementations
- Covariance, contravariance, and invariance
- Type-level natural numbers
- Implementing type-checked DSLs
- Linear types for resource safety

**Advanced Topics:**
- Type checker internals
- Unification algorithm
- Constraint generation and solving
- Effect inference

---

### 4. [Economics-as-Code](04-economics-as-code.md)

**Level:** Expert
**Duration:** 5-6 hours
**Prerequisites:** Advanced type system, linear programming basics

Use Eclexia for computational economics and quantitative research:
- Shadow pricing theory and dual variables
- Linear and integer programming
- Market equilibrium models
- Optimal resource allocation
- Dynamic pricing and demand response
- Carbon markets and emissions trading
- Auction mechanisms and mechanism design
- Agent-based economic modeling

**Topics Covered:**
- Dual simplex algorithm for shadow prices
- LP standard form and revised simplex
- Supply, demand, and Walrasian tatonnement
- Pareto efficiency and welfare maximization
- Real-time electricity pricing
- Cap-and-trade vs carbon tax
- Vickrey auctions and VCG mechanism
- Computable general equilibrium (CGE) models

**Research Applications:**
- Algorithmic mechanism design
- Climate economics simulation
- High-frequency trading strategies
- Energy market optimization
- Policy impact analysis

---

## Tutorial Format

Each tutorial includes:
- **Clear learning objectives** - What you'll be able to do
- **Comprehensive examples** - Working code you can run
- **Theory and practice** - Understanding plus hands-on experience
- **Best practices** - How to write idiomatic Eclexia
- **Practice exercises** - Reinforce your learning
- **Next steps** - Where to go from here

## Estimated Total Time

- **Beginner to Intermediate:** 5-7 hours (Tutorials 1-2)
- **Intermediate to Advanced:** 9-12 hours (Tutorials 1-3)
- **Complete Series:** 14-18 hours (All 4 tutorials)

## Prerequisites by Tutorial

| Tutorial | Programming | Economics | Math | Type Theory |
|----------|-------------|-----------|------|-------------|
| 1. Getting Started | Basic | None | None | None |
| 2. Resource-Aware | Intermediate | None | Basic algebra | None |
| 3. Advanced Types | Intermediate | None | Basic logic | Helpful |
| 4. Economics-as-Code | Intermediate | Helpful | Linear algebra | Optional |

## Additional Resources

### Reference Materials
- [Standard Library API Documentation](../stdlib-index.html)
- [Language Reference Manual](../reference/) (coming soon)
- [EBNF Grammar Specification](../reference/grammar.ebnf) (coming soon)

### Example Code
- [examples/](../../examples/) - Complete example programs
- [tests/conformance/](../../tests/conformance/) - Specification tests
- [stdlib/](../../stdlib/) - Standard library source code

### Community
- **GitHub**: [github.com/hyperpolymath/eclexia](https://github.com/hyperpolymath/eclexia)
- **Issues**: Report bugs and request features
- **Discussions**: Ask questions and share projects
- **Contributing**: See [CONTRIBUTING.md](../../CONTRIBUTING.md)

## Learning Tips

1. **Hands-on practice** - Type out the examples, don't just read
2. **Experiment** - Modify code to see what happens
3. **Read errors carefully** - Eclexia's error messages are designed to be helpful
4. **Start simple** - Master each concept before moving on
5. **Build projects** - Apply what you've learned to real problems
6. **Read stdlib code** - Learn from well-written Eclexia code
7. **Join the community** - Ask questions, share your work

## About These Tutorials

**Total Content:** ~22,000 words across 4 comprehensive tutorials

**Author:** Jonathan D.A. Jewell

**License:** PMPL-1.0-or-later

**Last Updated:** 2026-02-07

These tutorials are actively maintained and updated with new Eclexia features. If you find errors or have suggestions, please open an issue on GitHub.

---

**Ready to start?** Begin with [Getting Started with Eclexia](01-getting-started.md)!
