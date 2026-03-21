import Circ.AON.Defs

/-! # Internal: Lupanov Upper Bound Construction

The weak Lupanov bound: every Boolean function on `N` variables can be
computed by a fan-in-2 AND/OR circuit of size at most `C * 2^N / N`,
for a fixed constant `C` and all sufficiently large `N`.

## Proof Strategy

The construction uses the **column decomposition** with shared minterms.

### Parameters
- `k = ⌊log₂ N⌋ - 1` "address" variables (the first `k` inputs)
- `q = N - k` "data" variables (the remaining inputs)

### Decomposition
For any `f : {0,1}^N → {0,1}`, write input `x` as `(a, y)` where
`a ∈ {0,1}^k` and `y ∈ {0,1}^q`. Define:
- **Data minterm** `mᵧ` for `y ∈ {0,1}^q`: outputs `true` iff data variables equal `y`
- **Column function** `cᵧ : {0,1}^k → {0,1}` for `y`: `cᵧ(a) = f(a, y)`

Then `f(a, y) = ⋁ᵧ [mᵧ(data) ∧ cᵧ(addr)]`.

### Circuit Components and Gate Counts

1. **Data minterm tree** — shared binary prefix tree producing all `2^q` data minterms.
   Each internal node extends a partial minterm by one more variable (two ways:
   positive or negative). Starting from pairs of the first two data variables
   (4 = 2² base nodes), each subsequent variable doubles the nodes.
   Total: `≤ 2 · 2^q` gates.

2. **Address minterm tree** — analogous shared tree for the `k` address variables.
   Total: `≤ 2 · 2^k` gates.

3. **Pattern library** — for each distinct column function `cᵧ` (a function on
   `k` address variables), build an OR of the relevant address minterms.
   There are at most `2^(2^k)` distinct column functions (all possible functions
   on `k` bits). Each needs at most `2^k - 1` OR gates (binary OR tree over
   a subset of the shared address minterms).
   Total: `≤ 2^(2^k) · (2^k - 1) ≤ 2^(2^k + k)` gates.

4. **Combining AND layer** — for each data value `y ∈ {0,1}^q`, one AND gate
   computing `mᵧ(data) ∧ cᵧ(addr)`. The AND takes two inputs: the data
   minterm tree leaf for `y`, and the pattern library output for `cᵧ`.
   Total: `2^q` gates.

5. **Final OR tree** — binary tree of ORs combining all `2^q` terms.
   Total: `≤ 2^q` gates (including the output gate).

### Size Bound

Total internal gates `G ≤ 4 · 2^q + 2 · 2^k + 2^(2^k + k)`.
Circuit size `= G + 1` (single output gate).

For `N ≥ 16` with `k = ⌊log₂ N⌋ - 1`:
- `2^k ≥ N/4`, so `2^q = 2^(N-k) ≤ 4 · 2^N / N`, so `4 · 2^q ≤ 16 · 2^N / N`
- `2 · 2^k ≤ N`, and `N² ≤ 2^N` for `N ≥ 16`, so `2 · 2^k · N ≤ N² ≤ 2^N`
- `2^(2^k + k) · N ≤ 2^N` for `N ≥ 16` (since `N ≤ 2^(N - 2^k - k)`)
- `1 · N ≤ 2^N`

Summing: `(G + 1) · N ≤ (16 + 1 + 1 + 1) · 2^N = 19 · 2^N ≤ 20 · 2^N`,
which gives `G + 1 ≤ 20 · 2^N / N`.

### Correctness

The circuit computes `f` because the decomposition
`f(a, y) = ⋁ᵧ [mᵧ(data) ∧ cᵧ(addr)]` is a tautology: for any input `(a₀, y₀)`,
exactly one data minterm `mᵧ₀` fires (for `y = y₀`), and the AND with
`cᵧ₀(a₀) = f(a₀, y₀)` produces the correct value.
-/

namespace Lupanov

-- ════════════════════════════════════════════════════════════════
-- Section 1: Lupanov Decomposition Parameters
-- ════════════════════════════════════════════════════════════════

/-- Number of address variables in the Lupanov decomposition.
    Equal to `⌊log₂ N⌋ - 1` for `N ≥ 4`. -/
def addrBits (N : Nat) : Nat := Nat.log 2 N - 1

/-- Number of data variables in the Lupanov decomposition.
    Equal to `N - addrBits N`. -/
def dataBits (N : Nat) : Nat := N - addrBits N

-- ════════════════════════════════════════════════════════════════
-- Section 2: Circuit Construction Sub-Lemmas
-- ════════════════════════════════════════════════════════════════

/-! ### Binary Gate Composition

Given two single-output circuits `c₁` (with `G₁` internal gates) and `c₂`
(with `G₂` internal gates), construct a circuit that applies a binary
operation (AND or OR) to their outputs.

**Wire layout** of the composed circuit (`G = G₁ + 1 + G₂ + 1` internal gates):
- Wires `0 .. N-1`: primary inputs (shared)
- Wires `N .. N+G₁-1`: `c₁` internal gates (same wiring)
- Wire `N+G₁`: `c₁` output gate (internalized)
- Wires `N+G₁+1 .. N+G₁+G₂`: `c₂` internal gates (wire indices shifted by `G₁+1`)
- Wire `N+G₁+G₂+1`: `c₂` output gate (internalized, shifted)
- Output gate: `op(wire[N+G₁], wire[N+G₁+G₂+1])`

**Acyclicity**: Each `c₂` gate `j` originally references wires `< N + j`.
After shifting, its references become `< N + (G₁+1) + j = N + G₁ + 1 + j`,
which is exactly its new position. ✓ -/
theorem circuit_binop (op : AONOp) {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (f₁ f₂ : BitString N → Bool)
    (h₁ : (fun x => (c₁.eval x) 0) = f₁)
    (h₂ : (fun x => (c₂.eval x) 0) = f₂) :
    ∃ G (c : Circuit Basis.andOr2 N 1 G),
      (fun x => (c.eval x) 0) = (fun x =>
        match op with
        | .and => f₁ x && f₂ x
        | .or => f₁ x || f₂ x) ∧
      G + 1 = (G₁ + 1) + (G₂ + 1) + 1 := by
  sorry

/-! ### Chain of ORs

Given `n ≥ 1` single-output circuits computing `f₁, …, fₙ`, construct a
circuit computing `f₁ ∨ f₂ ∨ ⋯ ∨ fₙ` by cascading binary ORs.

The total internal gate count is the sum of all sub-circuit internal gates
plus `n - 1` additional OR gates for the cascade, plus `n` gates from
internalizing sub-circuit output gates. -/
theorem circuit_or_chain {N : Nat} [NeZero N]
    (n : Nat) (hn : 0 < n)
    (circuits : Fin n → Σ G, Circuit Basis.andOr2 N 1 G)
    (fs : Fin n → (BitString N → Bool))
    (hfs : ∀ i, (fun x => ((circuits i).2.eval x) 0) = fs i) :
    ∃ G (c : Circuit Basis.andOr2 N 1 G),
      (fun x => (c.eval x) 0) =
        (fun x => decide (∃ i : Fin n, fs i x = true)) ∧
      G + 1 ≤ (Finset.univ.sum fun i => (circuits i).1 + 1) + n := by
  sorry

/-! ### Minterm Circuit

A circuit that outputs `true` if and only if `m` selected input variables
match a target assignment. Uses a chain of `m - 1` AND gates (for `m ≥ 2`),
or a single self-AND gate (for `m = 1`).

For `Basis.andOr2`, each AND gate takes two inputs with optional per-input
negation. The negation flags encode the target bits: `neg i = !target i`
(negate the input wire when the target bit is `false`). -/
theorem circuit_minterm {N : Nat} [NeZero N]
    (m : Nat) (hm : 0 < m) (hmN : m ≤ N)
    (vars : Fin m → Fin N) (target : BitString m)
    (hinj : Function.Injective vars) :
    ∃ G (c : Circuit Basis.andOr2 N 1 G),
      (fun x => (c.eval x) 0) =
        (fun x => decide (∀ i : Fin m, x (vars i) = target i)) ∧
      G + 1 ≤ m := by
  sorry

/-! ### Shared Minterm Tree

Build all `2^m` minterms for `m` selected variables simultaneously, using a
shared binary prefix tree. This is the key to the Lupanov construction's
efficiency: instead of building each minterm independently (cost `m` per
minterm, total `m · 2^m`), the tree shares prefix computations (total
`≤ 2 · 2^m` gates).

The tree has `m - 1` levels. Level 1 produces 4 nodes (all 2-bit combos
of the first two variables). Each subsequent level extends every existing
node two ways (positive/negative on the next variable), doubling the count.

**Output**: A multi-output circuit (`M = 2^m`) where output `j` is the
minterm for the `j`-th assignment (bits of `j` encode the target). -/
theorem circuit_minterm_tree {N : Nat} [NeZero N]
    (m : Nat) (hm : 2 ≤ m) (hmN : m ≤ N)
    (vars : Fin m → Fin N) (hinj : Function.Injective vars) :
    ∃ G (c : Circuit Basis.andOr2 N (2 ^ m) G),
      (∀ (j : Fin (2 ^ m)) (x : BitString N),
        (c.eval x) j = decide (∀ i : Fin m, x (vars i) = j.val.testBit i.val)) ∧
      G + 2 ^ m ≤ 2 * 2 ^ m := by
  sorry

/-! ### Column Function Circuit

Given `k` address variables and a column function `col : BitString k → Bool`,
build a circuit computing `col` by OR-ing the relevant address minterms.

Assumes the address minterms are already built (as part of a larger circuit).
The column function is an OR over the subset of address assignments where
`col` is `true`, requiring at most `2^k - 1` OR gates. -/
theorem circuit_column_fn {N : Nat} [NeZero N]
    (k : Nat) (hk : 2 ≤ k) (hkN : k ≤ N)
    (col : BitString k → Bool) :
    ∃ G (c : Circuit Basis.andOr2 N 1 G),
      (fun x => (c.eval x) 0) =
        (fun x => col (fun i => x ⟨i.val, by omega⟩)) ∧
      G + 1 ≤ 2 ^ k := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- Section 3: Full Lupanov Assembly
-- ════════════════════════════════════════════════════════════════

/-! ### Lupanov Assembly

Combine the components into a single circuit computing `f`:

1. Build data minterm tree (all `2^q` data minterms): `≤ 2 · 2^q` gates
2. Build address minterm tree (all `2^k` address minterms): `≤ 2 · 2^k` gates
3. Build pattern library (one column fn circuit per distinct pattern):
   `≤ 2^(2^k + k)` gates
4. For each data value `y`: AND data minterm with column output: `2^q` gates
5. OR all terms: `≤ 2^q` gates

Total `G ≤ 4 · 2^q + 2 · 2^k + 2^(2^k + k)`. -/
theorem lupanov_assembly (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G (c : Circuit Basis.andOr2 N 1 G),
      (fun x => (c.eval x) 0) = f ∧
      G ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- Section 4: Arithmetic Size Bound
-- ════════════════════════════════════════════════════════════════

/-! ### Parameter Bounds

Key properties of `k = ⌊log₂ N⌋ - 1` for `N ≥ 16`:
- `k ≥ 3` (since `⌊log₂ 16⌋ = 4`)
- `2^k ≥ N / 4` (since `2^⌊log₂ N⌋ ≥ N / 2`)
- `q = N - k ≥ N - ⌊log₂ N⌋ + 1`
- `2^q ≤ 4 · 2^N / N`
-/

-- Proof sketch: 2^4 = 16 ≤ N, so Nat.log 2 N ≥ 4, so addrBits N ≥ 3.
theorem addrBits_ge_three (N : Nat) (hN : 16 ≤ N) :
    3 ≤ addrBits N := by
  unfold addrBits
  have h16 : 2 ^ 4 ≤ N := by omega
  have h4 : 4 ≤ Nat.log 2 N := Nat.le_log (by omega : 1 < 2) h16
  omega

-- Proof sketch: Nat.log 2 N ≤ N for all N, so dataBits N = N - (log₂ N - 1) > 0.
theorem dataBits_pos (N : Nat) (hN : 16 ≤ N) :
    0 < dataBits N := by
  unfold dataBits addrBits
  have : Nat.log 2 N < N := Nat.log_lt (by omega : 1 < 2) (by omega : 0 < N)
  omega

/-! ### Main Arithmetic Inequality

For `N ≥ 16`:
```
(4 · 2^q + 2 · 2^k + 2^(2^k+k) + 1) · N ≤ 20 · 2^N
```

This is established term by term:
- `4 · 2^q · N = 4N · 2^N / 2^k ≤ 16 · 2^N` (since `N / 2^k ≤ 4`)
- `2 · 2^k · N ≤ N² ≤ 2^N` (since `2^k ≤ N/2` and `N² ≤ 2^N` for `N ≥ 16`)
- `2^(2^k+k) · N ≤ 2^N` (since `N ≤ 2^(N - 2^k - k)` for `N ≥ 16`)
- `1 · N ≤ 2^N` (trivially)

Sum: `≤ (16 + 1 + 1 + 1) · 2^N = 19 · 2^N ≤ 20 · 2^N`. -/
theorem lupanov_arithmetic (N : Nat) (hN : 16 ≤ N) :
    (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
      2 ^ (2 ^ addrBits N + addrBits N) + 1) * N ≤ 20 * 2 ^ N := by
  sorry

/-! ### Size Bound Derivation -/

-- Proof: from the gate bound and the arithmetic inequality, derive the
-- division-form bound using Nat.le_div_iff_mul_le.
theorem lupanov_size_le (N : Nat) (hN : 16 ≤ N) (G : Nat)
    (hG : G ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
            2 ^ (2 ^ addrBits N + addrBits N)) :
    G + 1 ≤ 20 * 2 ^ N / N := by
  have hNpos : 0 < N := by omega
  -- Suffices to show (G + 1) * N ≤ 20 * 2^N
  suffices h : (G + 1) * N ≤ 20 * 2 ^ N by
    exact Nat.le_div_of_mul_le hNpos h
  calc (G + 1) * N
      ≤ (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) + 1) * N := by
        apply Nat.mul_le_mul_right; omega
    _ ≤ 20 * 2 ^ N := lupanov_arithmetic N hN

-- ════════════════════════════════════════════════════════════════
-- Section 5: Main Construction Theorem
-- ════════════════════════════════════════════════════════════════

/-- **Lupanov circuit construction**: For any Boolean function on `N ≥ 16`
    inputs, there exists a fan-in-2 AND/OR circuit of size at most
    `20 * 2^N / N` computing it.

    This follows from the Lupanov assembly (which constructs the circuit
    and bounds its internal gate count) and the arithmetic size bound
    (which converts the gate count to the `C * 2^N / N` form). -/
theorem lupanov_construction (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G (c : Circuit Basis.andOr2 N 1 G),
      (fun x => (c.eval x) 0) = f ∧ c.size ≤ 20 * 2 ^ N / N := by
  obtain ⟨G, c, heval, hG⟩ := lupanov_assembly N hN f
  exact ⟨G, c, heval, by rw [Circuit.size]; exact lupanov_size_le N hN G hG⟩

end Lupanov
