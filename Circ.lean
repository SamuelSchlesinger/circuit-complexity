import Circ.Basic
import Circ.NF
import Circ.AON
import Circ.XOR
import Circ.EssentialInput
import Circ.Shannon
import Circ.LowerBound
import Circ.Schnorr

/-! # Circuit Complexity Library

A Lean 4 formalization of classical results in Boolean circuit complexity,
built on Mathlib.

## The circuit model

A `Circuit B N M G` is an acyclic Boolean circuit over basis `B` with `N`
primary inputs, `M` outputs, and `G` internal gates. The circuit's `size`
is `G + M` (total gate count). The `size_complexity` of a Boolean function
is the minimum size of any circuit computing it.

## Main results

* **Functional completeness** (`CompleteBasis Basis.unboundedAON`):
  Unbounded fan-in AND/OR (with free negation) can compute every Boolean
  function, via DNF construction.

* **Shannon counting lower bound** (`shannon_lower_bound_circuit`):
  For `N ≥ 6`, there exists a Boolean function on `N` inputs that cannot
  be computed by any fan-in-2 AND/OR circuit with fewer than `2^N / (5N)`
  gates.

* **Gate elimination lower bound** (`Circuit.gate_elimination_lower_bound`):
  Any circuit over bounded fan-in `k` AND/OR computing a function with `n'`
  essential inputs has size at least `n' / k`.

* **Schnorr's XOR lower bound** (`schnorr_lower_bound_circuit`):
  Any fan-in-2 AND/OR circuit computing N-input XOR (or its complement)
  requires at least `2(N − 1)` internal gates.

## Module structure

Public modules (definitions a reviewer should read):

* `Circ.Basic` — `Circuit`, `Basis`, `Gate`, `CompleteBasis`, `size_complexity`
* `Circ.AON.Defs` — `AONOp`, `Basis.unboundedAON`, `Basis.boundedAON`, `Basis.andOr2`
* `Circ.NF` — `Literal`, `CNF`, `DNF`, `CNF.complexity`, `DNF.complexity`,
  `CNF.toCircuit`, `DNF.toCircuit`
* `Circ.XOR` — `Schnorr.xorBool` (N-input parity)
* `Circ.EssentialInput` — `IsEssentialInput`, `EssentialInputs`

Theorem modules (re-export definitions + main results):

* `Circ.AON` — functional completeness of AND/OR
* `Circ.Shannon` — Shannon counting lower bound
* `Circ.LowerBound` — gate elimination lower bound
* `Circ.Schnorr` — Schnorr's XOR lower bound

Internal modules contain proof machinery (CircDesc, DNF construction,
restriction/elimination arguments) and are not intended for direct use.
-/
