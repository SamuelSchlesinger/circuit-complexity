import Mathlib.Data.Nat.Lattice

/-! # Boolean Circuit Complexity

This file defines Boolean circuits parameterized by a basis of operations and
establishes the circuit size complexity measure for Boolean functions.

## Main definitions

* `Basis` — a basis of Boolean operations with arity constraints
* `Circuit` — an acyclic Boolean circuit (well-formedness by construction)
* `CompleteBasis` — typeclass for functionally complete bases
* `Circuit.size_complexity` — minimum circuit size computing a given function

## Main results

* `Circuit.size_complexity_pos` — for complete bases, size complexity is positive
-/

/-- Arity constraint for operations in a basis. -/
inductive Arity where
  | unbounded
  | exactly (k : Nat)
  | upto (k : Nat)
  deriving Repr, DecidableEq

/-- Whether `n` inputs satisfies an arity constraint. -/
def Arity.satisfiedBy : Arity → Nat → Prop
  | .unbounded, _ => True
  | .exactly k, n => n = k
  | .upto k, n => n ≤ k

instance (a : Arity) (n : Nat) : Decidable (a.satisfiedBy n) := by
  cases a <;> simp only [Arity.satisfiedBy] <;> exact inferInstance

/--
A basis of Boolean operations.

Each operation has an arity constraint and an evaluation function that computes
the output bit from any valid number of input bits.
-/
structure Basis where
  /-- The type of operations (e.g., AND, OR, NOT). -/
  Op : Type
  /-- The arity constraint for each operation. -/
  arity : Op → Arity
  /-- Evaluate an operation on `n` input bits, given that `n` satisfies the arity. -/
  eval : (op : Op) → (n : Nat) → (arity op).satisfiedBy n → (Fin n → Bool) → Bool

/--
A gate in a circuit over basis `B` with `W` wires available as inputs.
The gate's fan-in must satisfy the arity constraint of its operation, and each
input is wired to one of the `W` available wires.
-/
structure Gate (B : Basis) (W : Nat) where
  op : B.Op
  fanIn : Nat
  arityOk : (B.arity op).satisfiedBy fanIn
  inputs : Fin fanIn → Fin W

/-- Evaluate a gate given a wire-value assignment. -/
def Gate.eval (g : Gate B W) (wireVal : Fin W → Bool) : Bool :=
  B.eval g.op g.fanIn g.arityOk (wireVal ∘ g.inputs)

/--
A Boolean circuit over basis `B` with `N` inputs, `M` outputs, and `G`
internal gates.

**Well-formedness by construction:**
- Internal gate `i` draws its inputs from `Fin (N + i)` — the `N` primary
  inputs plus the outputs of internal gates `0, …, i − 1`. This makes
  cycles impossible at the type level.
- Each gate's fan-in is statically checked against the arity constraint
  of its operation.
- Each output gate draws from all `N + G` wires.
-/
structure Circuit (B : Basis) (N M G : Nat) [NeZero N] [NeZero M] where
  gates : (i : Fin G) → Gate B (N + i.val)
  outputs : Fin M → Gate B (N + G)

namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-- Value of wire `w` when the circuit is fed `input`.

The first `N` wires carry the primary inputs. Wire `N + i` carries the
output of internal gate `i`. -/
def wireValue (c : Circuit B N M G) (input : Fin N → Bool)
    (w : Fin (N + G)) : Bool :=
  if h : w.val < N then
    input ⟨w.val, h⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    B.eval gate.op gate.fanIn gate.arityOk
      fun i => c.wireValue input ⟨(gate.inputs i).val, by omega⟩
termination_by w.val
decreasing_by
  have := (gate.inputs i).isLt
  omega

/-- Evaluate a circuit: map an `N`-bit input to an `M`-bit output. -/
def eval (c : Circuit B N M G) (input : Fin N → Bool) : Fin M → Bool :=
  fun j => (c.outputs j).eval (c.wireValue input)

/-- The size of a circuit is its total number of gates (internal + output). -/
def size (_ : Circuit B N M G) : Nat := G + M

end Circuit

/-- A basis is complete if every Boolean function can be computed by some circuit over it. -/
class CompleteBasis (B : Basis) : Prop where
  complete : ∀ {N M} [NeZero N] [NeZero M] (f : (Fin N → Bool) → (Fin M → Bool)),
    ∃ G, ∃ c : Circuit B N M G, c.eval = f

namespace Circuit
variable {B : Basis} {N M : Nat} [NeZero N] [NeZero M]

/-- The minimum size circuit over basis `B` computing a given function.
    Returns 0 if no circuit over `B` computes `f`. -/
noncomputable def size_complexity
    (B : Basis) (f : (Fin N → Bool) → (Fin M → Bool)) : Nat :=
  sInf {s | ∃ G, ∃ c : Circuit B N M G, c.size = s ∧ c.eval = f}

private theorem size_complexity_set_nonempty [CompleteBasis B]
    (f : (Fin N → Bool) → (Fin M → Bool)) :
    {s | ∃ G, ∃ c : Circuit B N M G, c.size = s ∧ c.eval = f}.Nonempty :=
  let ⟨G, c, hc⟩ := CompleteBasis.complete (B := B) f
  ⟨c.size, G, c, rfl, hc⟩

/-- For a complete basis, circuit size complexity is always positive. -/
theorem size_complexity_pos [CompleteBasis B]
    (f : (Fin N → Bool) → (Fin M → Bool)) :
    0 < size_complexity B f := by
  obtain ⟨_, _, hs, _⟩ := Nat.sInf_mem (size_complexity_set_nonempty (B := B) f)
  simp only [size_complexity]
  rw [← hs, size]
  exact Nat.add_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne M))

end Circuit
