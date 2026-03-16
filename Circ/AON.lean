import Circ.AON.Defs
import Circ.Internal.AON
import Circ.Internal.Simulation

/-! # AND/OR/NOT Basis

This module provides the AND/OR basis definitions and completeness results.

## Definitions (from `Circ.AON.Defs`)

* `AONOp` — AND/OR operations
* `Basis.unboundedAON` — unbounded fan-in AND/OR basis
* `Basis.boundedAON k` — fan-in ≤ `k` AND/OR basis
* `Basis.andOr2` — fan-in exactly 2 AND/OR basis

## Main results

* `CompleteBasis Basis.unboundedAON` — proved via DNF construction
* `CompleteBasis Basis.andOr2` — proved via gate-chain simulation
  from `unboundedAON`, using `CompleteBasis.of_simulation`
-/
