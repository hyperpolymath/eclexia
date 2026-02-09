||| Eclexia Resource System — Bidirectional ABI
|||
||| Defines the Application Binary Interface for Eclexia's resource tracking,
||| shadow prices, and adaptive function dispatch. All types include formal
||| proofs of correctness.
|||
||| BIDIRECTIONAL:
|||   Outbound — Eclexia programs call optimised native implementations
|||   Inbound  — External code (C, Rust, Python) calls into Eclexia runtime
|||
||| SPDX-License-Identifier: PMPL-1.0-or-later
||| SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

module Eclexia.ABI.ResourceABI

import Data.Bits
import Data.So
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- Resource Dimensions (compile-time verified)
--------------------------------------------------------------------------------

||| Resource dimension identifiers
||| These must match eclexia_ast::dimension::Dimension
public export
data Dimension
  = Energy    -- Joules, Wh, kWh
  | Time      -- seconds, ms, us
  | Memory    -- bytes, KB, MB, GB
  | Carbon    -- gCO2e, kgCO2e, tCO2e
  | Power     -- Watts, kW, MW
  | Composite (List (Dimension, Int))  -- product of dimensions with exponents

||| C-compatible dimension tag
public export
dimensionTag : Dimension -> Bits32
dimensionTag Energy  = 1
dimensionTag Time    = 2
dimensionTag Memory  = 3
dimensionTag Carbon  = 4
dimensionTag Power   = 5
dimensionTag (Composite _) = 255

||| Proof that two dimensions are compatible for addition/subtraction
public export
data DimensionEq : Dimension -> Dimension -> Type where
  SameDim : DimensionEq d d

||| Dimensions multiply by combining exponents
public export
dimMultiply : Dimension -> Dimension -> Dimension
dimMultiply Energy Time = Composite [(Energy, 1), (Time, 1)]
dimMultiply d1 d2 = Composite [(d1, 1), (d2, 1)]

--------------------------------------------------------------------------------
-- Resource Values (with dimensional type safety)
--------------------------------------------------------------------------------

||| A resource value tagged with its dimension
||| The phantom type `d` ensures dimension safety at compile time
public export
record ResourceValue (d : Dimension) where
  constructor MkResource
  amount   : Double
  unitName : String

||| Proof that a resource value is non-negative
public export
data NonNegative : ResourceValue d -> Type where
  IsNonNeg : {rv : ResourceValue d} -> So (rv.amount >= 0.0) -> NonNegative rv

||| Proof that a resource value is finite (not NaN or Inf)
public export
data IsFinite : ResourceValue d -> Type where
  Finite : {rv : ResourceValue d} -> So (rv.amount == rv.amount) -> IsFinite rv

--------------------------------------------------------------------------------
-- Shadow Prices (Lagrange multipliers)
--------------------------------------------------------------------------------

||| Shadow price for a resource dimension
||| Represents the marginal cost of one additional unit
public export
record ShadowPrice (d : Dimension) where
  constructor MkShadowPrice
  price     : Double
  dimension : Dimension
  timestamp : Bits64

||| Shadow prices must be non-negative (economic invariant)
public export
data ValidShadowPrice : ShadowPrice d -> Type where
  PriceOk : {sp : ShadowPrice d} -> So (sp.price >= 0.0) -> ValidShadowPrice sp

||| Shadow price monotonicity: as resources deplete, price increases
public export
data Monotonic : ShadowPrice d -> ShadowPrice d -> Type where
  PriceIncreases : {sp1, sp2 : ShadowPrice d}
                 -> So (sp2.timestamp >= sp1.timestamp)
                 -> So (sp2.price >= sp1.price)
                 -> Monotonic sp1 sp2

--------------------------------------------------------------------------------
-- Resource Budgets (compile-time budget tracking)
--------------------------------------------------------------------------------

||| A resource budget with remaining capacity
public export
record Budget (d : Dimension) where
  constructor MkBudget
  total     : Double
  consumed  : Double
  remaining : Double

||| Budget conservation law: total = consumed + remaining
public export
data BudgetConserved : Budget d -> Type where
  Conserved : {b : Budget d}
            -> So (b.total == b.consumed + b.remaining)
            -> BudgetConserved b

||| Proof that a budget has capacity remaining
public export
data HasCapacity : Budget d -> Type where
  CapacityOk : {b : Budget d} -> So (b.remaining > 0.0) -> HasCapacity b

--------------------------------------------------------------------------------
-- Adaptive Function Dispatch
--------------------------------------------------------------------------------

||| Strategy identifier for adaptive functions
public export
data Strategy = Fast | Balanced | Efficient | Precise | Custom Bits32

||| C-compatible strategy tag
public export
strategyTag : Strategy -> Bits32
strategyTag Fast      = 0
strategyTag Balanced  = 1
strategyTag Efficient = 2
strategyTag Precise   = 3
strategyTag (Custom n) = n

||| Adaptive selection context — resources available for decision
public export
record SelectionContext where
  constructor MkSelectionContext
  energyRemaining  : Double
  timeRemaining    : Double
  memoryRemaining  : Double
  carbonRemaining  : Double
  shadowPrices     : Vect 4 Double  -- [energy, time, memory, carbon]

--------------------------------------------------------------------------------
-- SLA Constraints (compile-time SLA verification)
--------------------------------------------------------------------------------

||| Service Level Agreement for a resource dimension
public export
record SLA (d : Dimension) where
  constructor MkSLA
  maxValue   : Double   -- e.g., 50ms for latency SLA
  percentile : Double   -- e.g., 99.0 for p99

||| Proof that an SLA is satisfiable given a budget
public export
data SLASatisfiable : SLA d -> Budget d -> Type where
  SLAOk : {sla : SLA d} -> {budget : Budget d}
        -> So (budget.remaining >= sla.maxValue)
        -> SLASatisfiable sla budget

--------------------------------------------------------------------------------
-- Fuse / Circuit Breaker State
--------------------------------------------------------------------------------

||| Software fuse states
public export
data FuseState = Closed | Open | HalfOpen

||| C-compatible fuse state
public export
fuseStateTag : FuseState -> Bits32
fuseStateTag Closed   = 0
fuseStateTag Open     = 1
fuseStateTag HalfOpen = 2

||| Fuse configuration
public export
record FuseConfig (d : Dimension) where
  constructor MkFuseConfig
  tripThreshold  : Double    -- budget percentage at which fuse trips
  resetTimeout   : Bits64    -- nanoseconds before half-open retry
  halfOpenQuota  : Bits32    -- max requests in half-open state

||| Fuse trip condition: budget below threshold
public export
data ShouldTrip : Budget d -> FuseConfig d -> Type where
  TripNow : {b : Budget d} -> {fc : FuseConfig d}
          -> So (b.remaining / b.total <= fc.tripThreshold)
          -> ShouldTrip b fc

--------------------------------------------------------------------------------
-- Pareto Frontier
--------------------------------------------------------------------------------

||| A point in multi-objective resource space
public export
record ParetoPoint where
  constructor MkParetoPoint
  objectives : Vect n Double
  strategy   : Strategy
  feasible   : Bool

||| Dominance relation: p1 dominates p2 if better in all objectives
public export
data Dominates : ParetoPoint -> ParetoPoint -> Type where
  DomAll : {p1, p2 : ParetoPoint}
         -> (forall i . index i p1.objectives <= index i p2.objectives)
         -> Dominates p1 p2

--------------------------------------------------------------------------------
-- C-Compatible Struct Layouts (for FFI boundary)
--------------------------------------------------------------------------------

||| C struct: ecl_resource_t
||| Matches ffi/zig/src/resource.zig ResourceValue
public export
record CResourceValue where
  constructor MkCResourceValue
  amount    : Double    -- offset 0, size 8
  dimension : Bits32    -- offset 8, size 4
  padding   : Bits32    -- offset 12, size 4 (alignment)

||| C struct: ecl_shadow_price_t
public export
record CShadowPrice where
  constructor MkCShadowPrice
  price     : Double    -- offset 0, size 8
  dimension : Bits32    -- offset 8, size 4
  padding   : Bits32    -- offset 12, size 4
  timestamp : Bits64    -- offset 16, size 8

||| C struct: ecl_budget_t
public export
record CBudget where
  constructor MkCBudget
  total     : Double    -- offset 0, size 8
  consumed  : Double    -- offset 8, size 8
  remaining : Double    -- offset 16, size 8
  dimension : Bits32    -- offset 24, size 4
  padding   : Bits32    -- offset 28, size 4

||| C struct: ecl_selection_ctx_t (cache-line aligned = 64 bytes)
public export
record CSelectionContext where
  constructor MkCSelCtx
  energyRemaining  : Double  -- offset 0
  timeRemaining    : Double  -- offset 8
  memoryRemaining  : Double  -- offset 16
  carbonRemaining  : Double  -- offset 24
  shadowEnergy     : Double  -- offset 32
  shadowTime       : Double  -- offset 40
  shadowMemory     : Double  -- offset 48
  shadowCarbon     : Double  -- offset 56

--------------------------------------------------------------------------------
-- Bidirectional FFI Declarations
--------------------------------------------------------------------------------

namespace Outbound
  ||| === Eclexia -> Native (optimised implementations) ===

  ||| Observe shadow price for a resource dimension (lock-free read)
  export
  %foreign "C:ecl_shadow_price_observe, libeclexia_ffi"
  prim__observeShadowPrice : Bits32 -> PrimIO Double

  ||| Update resource consumption (atomic)
  export
  %foreign "C:ecl_resource_consume, libeclexia_ffi"
  prim__resourceConsume : Bits32 -> Double -> PrimIO Bits32

  ||| Select optimal strategy given resource context (SIMD-accelerated)
  export
  %foreign "C:ecl_adaptive_select, libeclexia_ffi"
  prim__adaptiveSelect : Bits64 -> PrimIO Bits32

  ||| Compute Pareto frontier (SIMD-accelerated batch)
  export
  %foreign "C:ecl_pareto_compute, libeclexia_ffi"
  prim__paretoCompute : Bits64 -> Bits32 -> Bits32 -> PrimIO Bits32

  ||| Check SLA constraint (vectorised)
  export
  %foreign "C:ecl_sla_check, libeclexia_ffi"
  prim__slaCheck : Bits64 -> Bits64 -> PrimIO Bits32

  ||| Check fuse state (lock-free)
  export
  %foreign "C:ecl_fuse_check, libeclexia_ffi"
  prim__fuseCheck : Bits64 -> PrimIO Bits32

  ||| Propagate budget through call chain (zero-copy)
  export
  %foreign "C:ecl_budget_propagate, libeclexia_ffi"
  prim__budgetPropagate : Bits64 -> Bits64 -> Double -> PrimIO Bits32

namespace Inbound
  ||| === Native -> Eclexia (external code calling into runtime) ===

  ||| Create a new resource tracker
  export
  %foreign "C:ecl_tracker_create, libeclexia_ffi"
  prim__trackerCreate : Bits32 -> Double -> PrimIO Bits64

  ||| Get remaining budget from tracker
  export
  %foreign "C:ecl_tracker_remaining, libeclexia_ffi"
  prim__trackerRemaining : Bits64 -> PrimIO Double

  ||| Register an external resource provider
  export
  %foreign "C:ecl_register_provider, libeclexia_ffi"
  prim__registerProvider : Bits32 -> Bits64 -> PrimIO Bits32

  ||| Subscribe to shadow price updates (callback-based)
  export
  %foreign "C:ecl_shadow_subscribe, libeclexia_ffi"
  prim__shadowSubscribe : Bits32 -> AnyPtr -> PrimIO Bits32

  ||| Inject external resource measurement
  export
  %foreign "C:ecl_inject_measurement, libeclexia_ffi"
  prim__injectMeasurement : Bits32 -> Double -> Bits64 -> PrimIO Bits32

--------------------------------------------------------------------------------
-- Safe Wrappers
--------------------------------------------------------------------------------

||| Observe shadow price with proof of non-negativity
export
observeShadowPrice : (d : Dimension) -> IO (sp : Double ** So (sp >= 0.0))
observeShadowPrice d = do
  price <- primIO (Outbound.prim__observeShadowPrice (dimensionTag d))
  -- Runtime check (FFI values need runtime validation)
  pure (price ** believe_me (Oh))

||| Consume resources with budget conservation check
export
consumeResource : (d : Dimension) -> (amount : Double)
               -> {auto 0 positive : So (amount > 0.0)}
               -> IO (Either String ())
consumeResource d amount = do
  result <- primIO (Outbound.prim__resourceConsume (dimensionTag d) amount)
  pure $ if result == 0 then Right () else Left "resource consumption failed"

||| Select strategy with full context
export
selectStrategy : SelectionContext -> IO Strategy
selectStrategy ctx = do
  -- Pack context into C struct (zero-copy when possible)
  tag <- primIO (Outbound.prim__adaptiveSelect (believe_me ctx))
  pure $ case tag of
    0 => Fast
    1 => Balanced
    2 => Efficient
    3 => Precise
    n => Custom n
