import Circ.AC0.Defs
import Circ.XOR

/-! # AC0 — The AC0 Complexity Class

This module re-exports the AC0 definitions and main results.

## Definitions (from `Circ.AC0.Defs`)

* `InAC0` — predicate: the family is in AC0 (constant depth, polynomial size,
  unbounded fan-in AND/OR)

## Main results

* `parity_not_in_AC0` — the parity function is not in AC0
-/

/-- The parity (XOR) function family: the `N`-input XOR for each input length. -/
def parityFamily : BoolFunFamily := fun N => Schnorr.xorBool N

/-- **Parity is not in AC0**.

The N-input XOR function cannot be computed by any constant-depth,
polynomial-size family of unbounded-fan-in AND/OR circuits. -/
theorem parity_not_in_AC0 : ¬InAC0 parityFamily := by
  sorry
