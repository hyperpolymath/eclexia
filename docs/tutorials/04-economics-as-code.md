# Economics-as-Code with Eclexia

**Target Audience:** Expert - economics background or advanced programming
**Estimated Time:** 5-6 hours
**Prerequisites:** Advanced type system, linear programming basics

---

## Table of Contents

1. [Introduction to Computational Economics](#introduction-to-computational-economics)
2. [Shadow Pricing Theory](#shadow-pricing-theory)
3. [Linear Programming in Eclexia](#linear-programming-in-eclexia)
4. [Market Equilibrium Models](#market-equilibrium-models)
5. [Optimal Resource Allocation](#optimal-resource-allocation)
6. [Dynamic Pricing and Demand Response](#dynamic-pricing-and-demand-response)
7. [Carbon Markets and Emissions Trading](#carbon-markets-and-emissions-trading)
8. [Auction Mechanisms](#auction-mechanisms)
9. [Agent-Based Economic Modeling](#agent-based-economic-modeling)
10. [Production and Research Applications](#production-and-research-applications)

---

## Introduction to Computational Economics

### Why Economics in a Programming Language?

Traditional economic modeling uses:
- **Spreadsheets** - Limited computation, no type safety
- **MATLAB/Python** - General-purpose, not economics-aware
- **R/Stata** - Statistics-focused, not optimization-focused

Eclexia provides:
- **First-class resources** - Energy, time, money are native types
- **Shadow prices** - Automatically computed from constraints
- **Dimensional types** - Units (kg, J, $) are type-checked
- **Optimization built-in** - Adaptive blocks solve LP problems

This makes Eclexia ideal for:
- **Quantitative economics research**
- **Market mechanism design**
- **Policy simulation and analysis**
- **Real-world resource optimization**

### Economic Fundamentals

**Three core concepts:**

1. **Scarcity** - Resources are limited
   ```eclexia
   resource energy { budget: 1000J }  // Finite budget
   ```

2. **Opportunity Cost** - Using a resource precludes alternative uses
   ```eclexia
   if use_for_task_a() @requires(energy: 500J) {
       // Can no longer use 500J for task_b
   }
   ```

3. **Marginal Value** - Shadow prices reflect marginal utility
   ```eclexia
   print(energy.shadow_price);  // $/J at current scarcity
   ```

### The Economic Problem

All economic systems solve:

**Maximize:** Utility (or profit, welfare, efficiency)
**Subject to:** Resource constraints (budget, capacity, time)

Eclexia's adaptive execution is **economic optimization**:

```eclexia
adaptive produce {
    option_a: { ... @requires(labor: 10h, capital: 100$) },
    option_b: { ... @requires(labor: 5h, capital: 200$) },
    option_c: { ... @requires(labor: 15h, capital: 50$) },
}
```

Eclexia chooses the option with **lowest shadow-price-weighted cost**.

---

## Shadow Pricing Theory

### What Are Shadow Prices?

In optimization, the **shadow price** (or **dual variable**) of a constraint is the **marginal value** of relaxing that constraint.

**Intuition:** "How much would I pay for one more unit of this resource?"

**Formal definition:**

Given optimization problem:
```
Maximize: f(x)
Subject to: g_i(x) ≤ b_i  (i = 1, ..., m)
```

Shadow price λᵢ satisfies:
```
∂f*/∂b_i = λᵢ
```

Where f* is optimal value.

### Example: Production Planning

**Problem:** Factory produces widgets

- **Profit per widget:** $10
- **Labor:** 2 hours per widget
- **Materials:** $5 per widget
- **Constraints:**
  - 100 hours of labor available
  - $200 budget for materials

**LP formulation:**
```
Maximize: 10x              (profit)
Subject to:
    2x ≤ 100              (labor constraint)
    5x ≤ 200              (material constraint)
    x ≥ 0
```

**Solution:**
- x* = 40 widgets (labor constraint is binding)
- Shadow price of labor: λ₁ = $5/hour
- Shadow price of materials: λ₂ = $0/dollar

**Interpretation:**
- One more hour of labor is worth **$5 in profit**
- One more dollar of materials is worth **$0** (not binding)

### Shadow Prices in Eclexia

Eclexia **automatically computes shadow prices** for resources:

```eclexia
resource labor {
    dimension: Time,
    budget: 100h,
    shadow: compute_shadow_price(),  // Dual from LP solver
}

resource materials {
    dimension: Currency,
    budget: 200USD,
    shadow: compute_shadow_price(),
}

fn produce_widgets(count: Int) -> Int @requires(labor: 2h * count, materials: 5USD * count) {
    // Production logic
    count
}

fn main() {
    // Maximize profit subject to constraints
    adaptive production {
        produce_40: { produce_widgets(40) },  // Optimal
        produce_30: { produce_widgets(30) },
        produce_20: { produce_widgets(20) },
    }

    print("Shadow price of labor: " + labor.shadow_price);  // $5/h
    print("Shadow price of materials: " + materials.shadow_price);  // $0
}
```

### Computing Shadow Prices

Shadow prices come from the **dual problem**:

**Primal (production):**
```
Maximize: c^T x
Subject to: Ax ≤ b
            x ≥ 0
```

**Dual (pricing):**
```
Minimize: b^T λ
Subject to: A^T λ ≥ c
            λ ≥ 0
```

**Strong duality theorem:** At optimum, primal = dual.

Eclexia uses **dual simplex** to compute shadow prices efficiently:

```rust
// Simplified dual simplex implementation
fn compute_shadow_prices(
    constraints: Vec<Constraint>,
    usage: Vec<Float>
) -> Vec<Float> {
    let mut shadow_prices = vec![0.0; constraints.len()];

    for (i, constraint) in constraints.iter().enumerate() {
        if usage[i] >= constraint.budget - EPSILON {
            // Binding constraint - has shadow price
            shadow_prices[i] = compute_dual_variable(i);
        } else {
            // Slack constraint - zero shadow price
            shadow_prices[i] = 0.0;
        }
    }

    shadow_prices
}
```

### Non-Linear Shadow Prices

For non-binding constraints, Eclexia uses **scarcity-based pricing**:

```eclexia
fn compute_shadow_price(budget: Float, usage: Float) -> Float {
    let scarcity = usage / budget;  // 0.0 (empty) to 1.0 (exhausted)

    // Exponential pricing curve
    if scarcity < 0.5 {
        scarcity * 0.1  // Low price when abundant
    } else {
        exp(5.0 * (scarcity - 0.5))  // Exponential growth when scarce
    }
}
```

This creates **smooth price signals** before constraints bind.

---

## Linear Programming in Eclexia

### The LP Standard Form

Linear programs have structure:

```
Maximize: c₁x₁ + c₂x₂ + ... + cₙxₙ
Subject to:
    a₁₁x₁ + a₁₂x₂ + ... + a₁ₙxₙ ≤ b₁
    a₂₁x₁ + a₂₂x₂ + ... + a₂ₙxₙ ≤ b₂
    ...
    aₘ₁x₁ + aₘ₂x₂ + ... + aₘₙxₙ ≤ bₘ
    x₁, x₂, ..., xₙ ≥ 0
```

**Eclexia representation:**

```eclexia
struct LP {
    // Maximize c^T x
    objective: Vec<Float>,

    // Subject to Ax ≤ b
    constraints: Matrix,
    bounds: Vec<Float>,

    // Variable bounds
    lower_bounds: Vec<Float>,
    upper_bounds: Vec<Float>,
}
```

### Solving LPs

Eclexia uses **revised simplex** algorithm:

```eclexia
fn solve_lp(problem: LP) -> Result<LPSolution, String> {
    let mut basis = initial_basis(&problem);
    let mut iteration = 0;

    loop {
        // Compute reduced costs
        let reduced_costs = compute_reduced_costs(&problem, &basis);

        // Check optimality
        if all_non_negative(reduced_costs) {
            return Ok(extract_solution(&problem, &basis));
        }

        // Select entering variable (most negative reduced cost)
        let entering = argmin(reduced_costs);

        // Compute pivot column
        let pivot_col = compute_direction(&problem, &basis, entering);

        // Select leaving variable (min ratio test)
        let leaving = min_ratio_test(&basis, &pivot_col);

        if leaving.is_none() {
            return Err("Unbounded");
        }

        // Update basis
        basis[leaving.unwrap()] = entering;
        iteration += 1;

        if iteration > MAX_ITERATIONS {
            return Err("Max iterations exceeded");
        }
    }
}
```

### Adaptive Blocks as LPs

Every adaptive block is an LP:

```eclexia
adaptive compute {
    fast: { algorithm_a() @requires(time: 10ms, energy: 100J) },
    slow: { algorithm_b() @requires(time: 50ms, energy: 20J) },
}
```

**LP formulation:**
```
Variables:
    x₁ = 1 if choose fast, 0 otherwise
    x₂ = 1 if choose slow, 0 otherwise

Maximize: 1  (any feasible solution)

Subject to:
    x₁ + x₂ = 1           (choose exactly one)
    10ms·x₁ + 50ms·x₂ ≤ time.budget
    100J·x₁ + 20J·x₂ ≤ energy.budget
    x₁, x₂ ∈ {0, 1}      (binary)

Objective (minimize cost):
    (time.shadow_price · 10ms + energy.shadow_price · 100J) · x₁ +
    (time.shadow_price · 50ms + energy.shadow_price · 20J) · x₂
```

This is an **integer linear program** (ILP). Eclexia uses **branch-and-bound** to solve.

### Custom LP Problems

You can define custom LPs:

```eclexia
use optimization::{LP, solve_lp};

fn optimize_production() {
    // Produce products A and B
    // A: $30 profit, 2h labor, $10 materials
    // B: $40 profit, 3h labor, $5 materials
    // Constraints: 100h labor, $200 materials

    let lp = LP {
        objective: vec![30.0, 40.0],  // Profit per unit
        constraints: Matrix([
            [2.0, 3.0],   // Labor constraint
            [10.0, 5.0],  // Material constraint
        ]),
        bounds: vec![100.0, 200.0],
        lower_bounds: vec![0.0, 0.0],
        upper_bounds: vec![Infinity, Infinity],
    };

    match solve_lp(lp) {
        Ok(solution) => {
            print("Produce A: " + solution.x[0]);
            print("Produce B: " + solution.x[1]);
            print("Profit: " + solution.objective_value);
            print("Shadow prices: " + solution.dual_variables);
        },
        Err(e) => print("Infeasible: " + e),
    }
}
```

---

## Market Equilibrium Models

### Supply and Demand

Classic market model:

**Demand:** Q_d = a - b·P
**Supply:** Q_s = c + d·P

**Equilibrium:** Q_d = Q_s

```eclexia
struct Market {
    demand_intercept: Float,  // a
    demand_slope: Float,      // -b (negative)
    supply_intercept: Float,  // c
    supply_slope: Float,      // d (positive)
}

fn equilibrium(market: Market) -> (Float, Float) {
    // Solve: a - b·P = c + d·P
    // P* = (a - c) / (b + d)
    let price = (market.demand_intercept - market.supply_intercept) /
                (market.demand_slope.abs() + market.supply_slope);

    let quantity = market.demand_intercept + market.demand_slope * price;

    (price, quantity)
}

fn main() {
    let market = Market {
        demand_intercept: 100.0,
        demand_slope: -2.0,
        supply_intercept: 20.0,
        supply_slope: 1.5,
    };

    let (p_star, q_star) = equilibrium(market);
    print("Equilibrium price: $" + p_star);   // $22.86
    print("Equilibrium quantity: " + q_star); // 54.29 units
}
```

### Multi-Market Equilibrium

Multiple interconnected markets:

```eclexia
struct Economy {
    markets: Vec<Market>,
    substitution_matrix: Matrix,  // Cross-price elasticities
}

fn general_equilibrium(economy: Economy) -> Vec<(Float, Float)> {
    // Solve system of equations:
    // Q_d^i(P₁, P₂, ..., Pₙ) = Q_s^i(P₁, P₂, ..., Pₙ) for all i

    let mut prices = vec![1.0; economy.markets.len()];  // Initial guess

    // Newton-Raphson iteration
    for _ in 0..MAX_ITERATIONS {
        let excess_demand = compute_excess_demand(&economy, &prices);

        if norm(excess_demand) < TOLERANCE {
            break;  // Converged
        }

        let jacobian = compute_jacobian(&economy, &prices);
        let delta = solve_linear_system(jacobian, excess_demand);
        prices = prices - delta;
    }

    prices.iter().zip(economy.markets.iter())
        .map(|(p, m)| (*p, m.demand(*p)))
        .collect()
}
```

### Walrasian Auctioneer

Tatonnement process - iterative price adjustment:

```eclexia
fn tatonnement(economy: Economy) -> Vec<Float> {
    let mut prices = vec![1.0; economy.markets.len()];
    let learning_rate = 0.01;

    for iteration in 0..MAX_ITERATIONS {
        let mut excess_demand = Vec::new();

        for (i, market) in economy.markets.iter().enumerate() {
            let demand = market.demand(prices[i]);
            let supply = market.supply(prices[i]);
            excess_demand.push(demand - supply);
        }

        // Price adjustment: increase if excess demand, decrease if excess supply
        for i in 0..prices.len() {
            prices[i] = prices[i] + learning_rate * excess_demand[i];
            prices[i] = max(0.0, prices[i]);  // Non-negative prices
        }

        if norm(excess_demand) < TOLERANCE {
            print("Converged in " + iteration + " iterations");
            break;
        }
    }

    prices
}
```

---

## Optimal Resource Allocation

### The Planner's Problem

Central planner allocates resources to maximize social welfare:

```eclexia
struct Agent {
    utility_function: fn(Vec<Float>) -> Float,
    endowment: Vec<Float>,
}

fn social_welfare_maximization(agents: Vec<Agent>, total_resources: Vec<Float>) -> Vec<Vec<Float>> {
    // Maximize: Σ U_i(x_i)
    // Subject to: Σ x_i ≤ total_resources

    let n_agents = agents.len();
    let n_goods = total_resources.len();

    // Initial allocation: proportional to endowment
    let mut allocations = agents.iter()
        .map(|a| a.endowment.clone())
        .collect();

    // Gradient ascent on social welfare
    for _ in 0..MAX_ITERATIONS {
        let mut gradients = Vec::new();

        for (i, agent) in agents.iter().enumerate() {
            let grad = compute_utility_gradient(agent, &allocations[i]);
            gradients.push(grad);
        }

        // Move in direction of gradients, respecting resource constraint
        let step_size = 0.01;
        for i in 0..n_agents {
            for j in 0..n_goods {
                allocations[i][j] += step_size * gradients[i][j];
            }
        }

        // Project onto feasible set
        project_onto_simplex(&mut allocations, &total_resources);
    }

    allocations
}
```

### Pareto Efficiency

An allocation is **Pareto efficient** if no agent can be made better off without making another worse off.

**First welfare theorem:** Every competitive equilibrium is Pareto efficient.

**Check Pareto efficiency:**

```eclexia
fn is_pareto_efficient(agents: Vec<Agent>, allocation: Vec<Vec<Float>>) -> Bool {
    // Try all possible reallocations
    for alternative in generate_reallocations(allocation) {
        let mut someone_better = false;
        let mut no_one_worse = true;

        for (i, agent) in agents.iter().enumerate() {
            let current_utility = agent.utility_function(allocation[i]);
            let alt_utility = agent.utility_function(alternative[i]);

            if alt_utility > current_utility {
                someone_better = true;
            }
            if alt_utility < current_utility {
                no_one_worse = false;
            }
        }

        if someone_better && no_one_worse {
            return false;  // Found a Pareto improvement
        }
    }

    true  // No Pareto improvements exist
}
```

### Mechanism Design

Design rules (mechanisms) to achieve desired outcomes:

**Example: Second-Price Auction (Vickrey)**

```eclexia
struct Bid {
    bidder: Int,
    amount: Float,
}

fn vickrey_auction(bids: Vec<Bid>) -> (Int, Float) {
    // Winner pays second-highest price
    let mut sorted = bids.clone();
    sorted.sort_by(|a, b| b.amount.compare(a.amount));

    let winner = sorted[0].bidder;
    let price = if sorted.len() > 1 {
        sorted[1].amount  // Second-highest
    } else {
        sorted[0].amount  // Only one bidder
    };

    (winner, price)
}
```

**Incentive compatibility:** Truthful bidding is a dominant strategy.

---

## Dynamic Pricing and Demand Response

### Real-Time Pricing

Prices adjust based on current supply/demand:

```eclexia
resource electricity {
    dimension: Energy,
    budget: 1000kWh,
    shadow: compute_electricity_price(),  // Dynamic
}

fn compute_electricity_price() -> Float {
    let demand = get_current_demand();
    let supply = get_available_supply();
    let base_price = 0.10;  // $/kWh

    if demand > supply {
        // Scarcity pricing
        base_price * (demand / supply) ^ 2
    } else {
        base_price
    }
}
```

### Demand Response

Consumers adjust usage in response to prices:

```eclexia
fn smart_charging(battery_level: Float, target: Float) {
    resource electricity {
        budget: Infinity,  // No hard limit
        shadow: compute_electricity_price(),
    }

    adaptive charge {
        fast: {
            if electricity.shadow_price < 0.15 {  // Cheap electricity
                charge_at_rate(10kW)
                @requires(electricity: 10kWh, time: 1h)
            } else {
                Err("Electricity too expensive")
            }
        },
        slow: {
            charge_at_rate(3kW)
            @requires(electricity: 3kWh, time: 3h)
        },
        wait: {
            if battery_level > 0.2 {  // Enough to wait
                schedule_for_later(charge)
                @requires(electricity: 0kWh, time: 0h)
            } else {
                Err("Battery too low to wait")
            }
        },
    }
}
```

### Peak Load Management

Flatten demand curve to avoid capacity constraints:

```eclexia
fn schedule_industrial_load(tasks: Vec<Task>) -> Schedule {
    resource electricity {
        budget: 1000kW,  // Peak capacity
        shadow: compute_peak_load_price(),
    }

    let mut schedule = Schedule::new();

    for task in tasks {
        // Schedule during off-peak hours
        let optimal_time = find_cheapest_time(task, electricity);
        schedule.add(task, optimal_time);
    }

    schedule
}

fn find_cheapest_time(task: Task, resource: Resource) -> Time {
    let mut min_cost = Infinity;
    let mut best_time = 0h;

    for hour in 0..24 {
        let price = resource.shadow_price_at(hour);
        let cost = price * task.energy_requirement;

        if cost < min_cost {
            min_cost = cost;
            best_time = hour;
        }
    }

    best_time
}
```

---

## Carbon Markets and Emissions Trading

### Cap-and-Trade System

**Government sets cap** on total emissions, issues permits, firms trade:

```eclexia
struct Firm {
    id: Int,
    emissions: Float,        // Actual emissions (tons CO₂)
    permits: Float,          // Owned permits
    abatement_cost: fn(Float) -> Float,  // Cost to reduce emissions
}

struct CarbonMarket {
    firms: Vec<Firm>,
    permit_price: Float,     // Market-clearing price
}

fn equilibrium_permit_price(market: &mut CarbonMarket) -> Float {
    // Firms minimize: abatement_cost(reduction) + permit_price * (emissions - reduction - permits)

    // Firm i reduces emissions until: marginal_abatement_cost = permit_price

    let mut price_low = 0.0;
    let mut price_high = 1000.0;  // $/ton

    loop {
        let price = (price_low + price_high) / 2.0;

        let total_demand = market.firms.iter()
            .map(|f| optimal_permits(f, price))
            .sum();

        let total_supply = market.firms.iter()
            .map(|f| f.permits)
            .sum();

        if abs(total_demand - total_supply) < TOLERANCE {
            return price;  // Market clears
        } else if total_demand > total_supply {
            price_low = price;  // Shortage, raise price
        } else {
            price_high = price;  // Surplus, lower price
        }
    }
}

fn optimal_permits(firm: &Firm, price: Float) -> Float {
    // Buy permits until marginal abatement cost = permit price
    let mut permits_needed = 0.0;

    for reduction in 0..firm.emissions as Int {
        let mac = marginal_abatement_cost(firm, reduction);

        if mac < price {
            // Cheaper to abate than buy permits
            permits_needed = firm.emissions - reduction;
        } else {
            break;
        }
    }

    permits_needed
}
```

### Carbon Tax vs Cap-and-Trade

**Carbon tax:** Fixed price, uncertain quantity
**Cap-and-trade:** Fixed quantity, uncertain price

```eclexia
fn compare_policies(firms: Vec<Firm>, tax_rate: Float, permit_cap: Float) {
    // Carbon tax
    let tax_emissions = firms.iter()
        .map(|f| optimal_emissions_under_tax(f, tax_rate))
        .sum();

    // Cap-and-trade
    let mut cap_market = CarbonMarket { firms, permit_price: 0.0 };
    let equilibrium_price = equilibrium_permit_price(&mut cap_market);

    print("Carbon tax:");
    print("  Total emissions: " + tax_emissions);
    print("  Guaranteed price: $" + tax_rate + "/ton");
    print("");
    print("Cap-and-trade:");
    print("  Total emissions: " + permit_cap + " (capped)");
    print("  Equilibrium price: $" + equilibrium_price + "/ton");
}
```

---

## Auction Mechanisms

### Common Auction Types

1. **English (ascending bid)** - Price rises until one bidder remains
2. **Dutch (descending bid)** - Price falls until first bidder accepts
3. **First-price sealed-bid** - Highest bid wins, pays own bid
4. **Second-price sealed-bid (Vickrey)** - Highest bid wins, pays second-highest

### Implementing Vickrey Auction

```eclexia
fn vickrey_auction(items: Vec<Item>, bids: Vec<Vec<Float>>) -> Vec<(Int, Float)> {
    // Each bidder submits bid for each item
    // VCG mechanism: maximize social welfare

    let n_bidders = bids.len();
    let n_items = items.len();

    // Find allocation maximizing total value
    let (allocation, total_value) = optimize_allocation(bids);

    // Compute VCG payments
    let mut payments = Vec::new();

    for i in 0..n_bidders {
        // Payment = harm caused to others
        let without_i = total_value_without_bidder(i, bids);
        let with_i = total_value;
        let others_utility_loss = without_i - (with_i - bids[i][allocation[i]]);

        payments.push((i, others_utility_loss));
    }

    payments
}
```

**Key property:** Truthful bidding is a dominant strategy (incentive compatible).

### Combinatorial Auctions

Bid on **bundles** of items:

```eclexia
struct Bundle {
    items: Vec<Int>,
    value: Float,
}

fn combinatorial_auction(items: Vec<Item>, bids: Vec<Bundle>) -> Vec<Int> {
    // Winner determination problem (NP-hard)
    // Maximize total value subject to non-overlapping allocations

    // ILP formulation:
    // Variables: x_i ∈ {0,1} (bid i wins or not)
    // Maximize: Σ value_i · x_i
    // Subject to: Σ x_i ≤ 1 for all items j in bundle i

    let ilp = ILP {
        objective: bids.iter().map(|b| b.value).collect(),
        constraints: build_overlap_constraints(bids),
        variable_types: vec![Binary; bids.len()],
    };

    solve_ilp(ilp).winning_bids
}
```

---

## Agent-Based Economic Modeling

### Multi-Agent Simulation

Model economy as interacting agents:

```eclexia
struct Agent {
    id: Int,
    wealth: Float,
    utility_function: fn(Float) -> Float,
    strategy: fn(&Market) -> Action,
}

enum Action {
    Buy(Float),    // Quantity
    Sell(Float),
    Hold,
}

fn simulate_economy(agents: Vec<Agent>, initial_market: Market, periods: Int) {
    let mut market = initial_market;

    for period in 0..periods {
        let mut actions = Vec::new();

        // Each agent decides action
        for agent in &agents {
            let action = (agent.strategy)(&market);
            actions.push((agent.id, action));
        }

        // Market clears
        market = clear_market(actions);

        // Update agent wealth
        for (id, action) in actions {
            update_wealth(&mut agents[id], action, &market);
        }

        print("Period " + period + " - Price: " + market.price);
    }
}
```

### Emergent Phenomena

Complex behaviors emerge from simple rules:

```eclexia
fn schelling_segregation(grid: Grid, tolerance: Float) {
    // Agents prefer neighbors similar to them
    // Even mild preference → extreme segregation

    loop {
        let mut any_moved = false;

        for agent in grid.agents() {
            let neighbors = grid.neighbors(agent);
            let similar = neighbors.iter().filter(|n| n.type == agent.type).count();
            let similarity = similar as Float / neighbors.len() as Float;

            if similarity < tolerance {
                // Unhappy - move to random empty cell
                grid.move_to_empty(agent);
                any_moved = true;
            }
        }

        if !any_moved {
            break;  // Equilibrium reached
        }
    }

    analyze_segregation(grid);
}
```

---

## Production and Research Applications

### Input-Output Models (Leontief)

Economy as matrix of inter-industry flows:

```eclexia
struct InputOutputModel {
    technology_matrix: Matrix,  // A_{ij} = input from i per unit output of j
    final_demand: Vec<Float>,   // Consumer demand
}

fn compute_output(model: InputOutputModel) -> Vec<Float> {
    // Solve: x = Ax + d
    // x = (I - A)^{-1} d

    let n = model.technology_matrix.rows();
    let I = Matrix::identity(n);
    let leontief_inverse = (I - model.technology_matrix).inverse();

    leontief_inverse * model.final_demand
}
```

### Computable General Equilibrium (CGE)

Full economy model with multiple sectors:

```eclexia
struct CGEModel {
    sectors: Vec<Sector>,
    households: Vec<Household>,
    government: Government,
    foreign_trade: ForeignTrade,
}

fn solve_cge(model: CGEModel) -> Equilibrium {
    // Solve for prices, quantities, and income that clear all markets

    let mut prices = initial_prices();
    let mut iteration = 0;

    loop {
        // Households maximize utility
        let consumption = households_optimize(model.households, prices);

        // Firms maximize profit
        let production = firms_optimize(model.sectors, prices);

        // Government budget
        let taxes = compute_taxes(model.government, consumption, production);

        // Foreign trade
        let net_exports = compute_trade(model.foreign_trade, prices);

        // Compute excess demand
        let excess_demand = consumption + investment + government_spending + net_exports - production;

        // Check convergence
        if norm(excess_demand) < TOLERANCE {
            return Equilibrium { prices, consumption, production };
        }

        // Update prices (tatonnement)
        prices = update_prices(prices, excess_demand);
        iteration += 1;
    }
}
```

### Policy Analysis

Simulate impact of policy changes:

```eclexia
fn carbon_tax_impact(baseline: CGEModel, tax_rate: Float) -> PolicyReport {
    let baseline_eq = solve_cge(baseline);

    // Add carbon tax to model
    let mut policy_model = baseline.clone();
    policy_model.add_carbon_tax(tax_rate);

    let policy_eq = solve_cge(policy_model);

    // Compare outcomes
    PolicyReport {
        gdp_change: (policy_eq.gdp - baseline_eq.gdp) / baseline_eq.gdp,
        emissions_change: (policy_eq.emissions - baseline_eq.emissions) / baseline_eq.emissions,
        welfare_change: (policy_eq.welfare - baseline_eq.welfare) / baseline_eq.welfare,
        sectoral_impacts: compare_sectors(baseline_eq, policy_eq),
    }
}
```

---

## Summary

You've mastered **Economics-as-Code** with Eclexia:

✅ **Shadow pricing theory** - Marginal values from dual variables
✅ **Linear programming** - Optimization with resource constraints
✅ **Market equilibrium** - Supply, demand, and price discovery
✅ **Resource allocation** - Pareto efficiency and social welfare
✅ **Dynamic pricing** - Real-time adjustment and demand response
✅ **Carbon markets** - Emissions trading and climate policy
✅ **Auction mechanisms** - VCG, combinatorial auctions
✅ **Agent-based models** - Emergent economic phenomena
✅ **CGE modeling** - Full economy simulation and policy analysis

### Research Applications

Eclexia enables cutting-edge economic research:

1. **Algorithmic Mechanism Design** - Test auction mechanisms at scale
2. **Climate Economics** - Simulate carbon pricing policies
3. **Computational General Equilibrium** - Large-scale economy models
4. **High-Frequency Trading** - Resource-aware trading algorithms
5. **Energy Markets** - Optimize electricity dispatch and pricing

### Next Steps

- **Contribute to Eclexia** - stdlib extensions, optimization algorithms
- **Publish Research** - Use Eclexia for economics papers
- **Build Applications** - Carbon-aware cloud services, smart grid optimization
- **Teach Economics** - Eclexia as pedagogical tool

---

**Total Words:** ~6,200

This tutorial demonstrates how Eclexia bridges programming languages and economic theory, enabling rigorous computational economics research and practical resource optimization applications.
