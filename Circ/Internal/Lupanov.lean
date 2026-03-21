import Circ.AON.Defs
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # Internal: Lupanov Upper Bound Construction

The weak Lupanov bound: every Boolean function on `N` variables can be
computed by a fan-in-2 AND/OR circuit of size at most `C * 2^N / N`,
for a fixed constant `C` and all sufficiently large `N`.

## Construction

Split `N` inputs into `k = ⌊log₂ N⌋ - 1` address variables and
`q = N - k` data variables. Decompose any `f : {0,1}^N → {0,1}` as
`f(a,y) = ⋁ᵧ [mintermᵧ(data) ∧ colᵧ(addr)]` where `colᵧ(a) = f(a,y)`.

Build shared minterm trees for both variable groups, a pattern library
for column functions, AND/OR combining layers. Total ≤ `20 · 2^N / N`
gates for `N ≥ 16`.
-/

namespace Lupanov

-- ════════════════════════════════════════════════════════════════
-- Section 1: Parameters
-- ════════════════════════════════════════════════════════════════

/-- Number of address variables: `⌊log₂ N⌋ - 1`. -/
def addrBits (N : Nat) : Nat := Nat.log 2 N - 1

/-- Number of data variables: `N - addrBits N`. -/
def dataBits (N : Nat) : Nat := N - addrBits N

-- ════════════════════════════════════════════════════════════════
-- Section 2: Gate Construction Helpers
-- ════════════════════════════════════════════════════════════════

/-- Build a fan-in-2 gate from two wire references and negation flags. -/
private def mkGate2 (op : AONOp) {W : Nat}
    (w₀ w₁ : Fin W) (n₀ n₁ : Bool) : Gate Basis.andOr2 W where
  op := op; fanIn := 2; arityOk := rfl
  inputs i := if i.val = 0 then w₀ else w₁
  negated i := if i.val = 0 then n₀ else n₁

/-- Remap a wire from c₂'s space into the combined space: primary inputs
    stay, internal wires shift by `G₁ + 1`. -/
private def remap₂ (N G₁ G₂ : Nat) (w : Fin (N + G₂)) : Fin (N + (G₁ + G₂ + 2)) :=
  if h : w.val < N then ⟨w.val, by omega⟩
  else ⟨w.val + G₁ + 1, by have := w.isLt; omega⟩

private def gw₀ {W : Nat} (g : Gate Basis.andOr2 W) : Fin W :=
  g.inputs ⟨0, by rw [andOr2_fanIn]; omega⟩
private def gw₁ {W : Nat} (g : Gate Basis.andOr2 W) : Fin W :=
  g.inputs ⟨1, by rw [andOr2_fanIn]; omega⟩
private def gn₀ {W : Nat} (g : Gate Basis.andOr2 W) : Bool :=
  g.negated ⟨0, by rw [andOr2_fanIn]; omega⟩
private def gn₁ {W : Nat} (g : Gate Basis.andOr2 W) : Bool :=
  g.negated ⟨1, by rw [andOr2_fanIn]; omega⟩

/-- Lift a wire from c₁'s space into the combined space (extend bound). -/
private def lift₁ {N G₁ G₂ : Nat} (w : Fin (N + G₁)) : Fin (N + (G₁ + G₂ + 2)) :=
  ⟨w.val, by omega⟩

-- ════════════════════════════════════════════════════════════════
-- Section 2b: Binary Circuit Composition
-- ════════════════════════════════════════════════════════════════

/-- Compose two circuits with a binary AND/OR. Produces `G₁ + G₂ + 2`
    internal gates by internalizing both circuits' output gates and adding
    a binary op gate as the new output.

    Gate layout: `[c₁.gates | c₁.out | c₂.gates(remapped) | c₂.out(remapped)]`
    Output: `op(wire[N+G₁], wire[N+G₁+G₂+1])`. -/
def binopCircuit (op : AONOp) {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂) :
    Circuit Basis.andOr2 N 1 (G₁ + G₂ + 2) where
  gates i :=
    if h₁ : i.val < G₁ then
      let g := c₁.gates ⟨i.val, h₁⟩
      mkGate2 g.op (lift₁ (gw₀ g)) (lift₁ (gw₁ g)) (gn₀ g) (gn₁ g)
    else if _ : i.val = G₁ then
      let g := c₁.outputs 0
      mkGate2 g.op (lift₁ (gw₀ g)) (lift₁ (gw₁ g)) (gn₀ g) (gn₁ g)
    else if h₃ : i.val < G₁ + 1 + G₂ then
      let g := c₂.gates ⟨i.val - G₁ - 1, by omega⟩
      mkGate2 g.op (remap₂ N G₁ G₂ (gw₀ g)) (remap₂ N G₁ G₂ (gw₁ g)) (gn₀ g) (gn₁ g)
    else
      let g := c₂.outputs 0
      mkGate2 g.op (remap₂ N G₁ G₂ (gw₀ g)) (remap₂ N G₁ G₂ (gw₁ g)) (gn₀ g) (gn₁ g)
  outputs _ := mkGate2 op ⟨N + G₁, by omega⟩ ⟨N + G₁ + G₂ + 1, by omega⟩ false false
  acyclic := by intro i k; sorry

-- ════════════════════════════════════════════════════════════════
-- Section 3: Full Lupanov Assembly (sorry'd)
-- ════════════════════════════════════════════════════════════════

/-- Full Lupanov circuit: `G ≤ 4·2^q + 2·2^k + 2^(2^k+k)` internal gates. -/
theorem lupanov_assembly (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧
      G ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) := by
  sorry

-- ════════════════════════════════════════════════════════════════
-- Section 4: Arithmetic — fully proved except term3
-- ════════════════════════════════════════════════════════════════

/-! ### Nat.log helpers -/

private theorem log_ge_one (N : Nat) (hN : 16 ≤ N) : 1 ≤ Nat.log 2 N :=
  Nat.le_log_of_pow_le (by omega) (by omega)

private theorem log_lt_N (N : Nat) (hN : 16 ≤ N) : Nat.log 2 N < N :=
  Nat.log_lt_of_lt_pow (by omega) (@Nat.lt_pow_self N 2 (by omega))

theorem addrBits_ge_three (N : Nat) (hN : 16 ≤ N) : 3 ≤ addrBits N := by
  unfold addrBits
  have := Nat.le_log_of_pow_le (by omega : 1 < 2) (show 2 ^ 4 ≤ N by omega)
  omega

theorem dataBits_pos (N : Nat) (hN : 16 ≤ N) : 0 < dataBits N := by
  unfold dataBits addrBits; have := log_lt_N N hN; omega

/-! ### Key identities -/

private theorem addr_le_N (N : Nat) (hN : 16 ≤ N) : addrBits N ≤ N := by
  unfold addrBits; have := log_lt_N N hN; omega

private theorem addr_data_sum (N : Nat) (hN : 16 ≤ N) :
    dataBits N + addrBits N = N := by
  unfold dataBits; have := addr_le_N N hN; omega

private theorem pow_split (N : Nat) (hN : 16 ≤ N) :
    2 ^ dataBits N * 2 ^ addrBits N = 2 ^ N := by
  rw [← Nat.pow_add]; congr 1; exact addr_data_sum N hN

private theorem two_mul_pow_addr_le (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N ≤ N := by
  unfold addrBits
  have hlog := log_ge_one N hN
  have : 2 * 2 ^ (Nat.log 2 N - 1) = 2 ^ Nat.log 2 N := by
    conv_rhs => rw [show Nat.log 2 N = (Nat.log 2 N - 1) + 1 from by omega]
    rw [Nat.pow_succ]; ring
  rw [this]; exact Nat.pow_log_le_self 2 (by omega)

private theorem n_lt_four_pow_addr (N : Nat) (hN : 16 ≤ N) :
    N < 4 * 2 ^ addrBits N := by
  unfold addrBits
  have hlog := log_ge_one N hN
  have : 4 * 2 ^ (Nat.log 2 N - 1) = 2 ^ (Nat.log 2 N + 1) := by
    conv_rhs => rw [show Nat.log 2 N + 1 = (Nat.log 2 N - 1) + 2 from by omega]
    rw [Nat.pow_add]; omega
  rw [this]; exact Nat.lt_pow_succ_log_self (by omega) N

/-! ### N² ≤ 2^N for N ≥ 16 -/

private theorem two_n_plus_one_le (N : Nat) (hN : 4 ≤ N) : 2 * N + 1 ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 4 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      calc 2 * (n + 1) + 1 = 2 * n + 1 + 2 := by ring
        _ ≤ 2 ^ n + 2 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by nlinarith [@Nat.lt_pow_self n 2 (by omega)]
        _ = 2 ^ (n + 1) := by ring

private theorem sq_le_pow (N : Nat) (hN : 16 ≤ N) : N * N ≤ 2 ^ N := by
  induction N with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 16 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      have := two_n_plus_one_le n (by omega)
      calc (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
        _ ≤ 2 ^ n + (2 * n + 1) := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by ring

/-! ### Term-by-term bounds -/

/-- `4 · 2^q · N ≤ 16 · 2^N` -/
private theorem term1 (N : Nat) (hN : 16 ≤ N) :
    4 * 2 ^ dataBits N * N ≤ 16 * 2 ^ N := by
  have hlt := n_lt_four_pow_addr N hN
  calc 4 * 2 ^ dataBits N * N
      ≤ 4 * 2 ^ dataBits N * (4 * 2 ^ addrBits N - 1) := by
        apply Nat.mul_le_mul_left; omega
    _ ≤ 4 * 2 ^ dataBits N * (4 * 2 ^ addrBits N) := by
        apply Nat.mul_le_mul_left; omega
    _ = 16 * (2 ^ dataBits N * 2 ^ addrBits N) := by ring
    _ = 16 * 2 ^ N := by rw [pow_split N hN]

/-- `2 · 2^k · N ≤ 2^N` -/
private theorem term2 (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N * N ≤ 2 ^ N := by
  calc 2 * 2 ^ addrBits N * N
      ≤ N * N := by apply Nat.mul_le_mul_right; exact two_mul_pow_addr_le N hN
    _ ≤ 2 ^ N := sq_le_pow N hN

/-- `4k ≤ 2^k` for `k ≥ 4`. -/
private theorem pow_ge_four_mul (k : Nat) (hk : 4 ≤ k) : 4 * k ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_or_ge n 4 with
    | inl h => interval_cases n <;> omega
    | inr h =>
      have := ih (by omega)
      calc 4 * (n + 1) = 4 * n + 4 := by ring
        _ ≤ 2 ^ n + 4 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by nlinarith [@Nat.lt_pow_self n 2 (by omega)]
        _ = 2 ^ (n + 1) := by ring

/-- `4 · log₂ N ≤ N` for `N ≥ 16`. Follows from `4k ≤ 2^k ≤ N` with `k = log₂ N`. -/
private theorem log_le_quarter (N : Nat) (hN : 16 ≤ N) : 4 * Nat.log 2 N ≤ N := by
  have hlog4 : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  calc 4 * Nat.log 2 N
      ≤ 2 ^ Nat.log 2 N := pow_ge_four_mul (Nat.log 2 N) hlog4
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

/-- The exponent `2^k + k` is small enough that `N` fits in the remaining bits. -/
private theorem pow_addr_plus_addr_le (N : Nat) (hN : 16 ≤ N) :
    2 ^ addrBits N + addrBits N + (Nat.log 2 N + 1) ≤ N := by
  unfold addrBits
  have hlog1 : 1 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  have : 2 * 2 ^ (Nat.log 2 N - 1) = 2 ^ Nat.log 2 N := by
    conv_rhs => rw [show Nat.log 2 N = (Nat.log 2 N - 1) + 1 from by omega]
    rw [Nat.pow_succ]; ring
  have : 2 * 2 ^ (Nat.log 2 N - 1) ≤ N := by
    rw [this]; exact Nat.pow_log_le_self 2 (by omega)
  have := log_le_quarter N hN
  omega

/-- `2^(2^k + k) · N ≤ 2^N` for `N ≥ 16` -/
private theorem term3 (N : Nat) (hN : 16 ≤ N) :
    2 ^ (2 ^ addrBits N + addrBits N) * N ≤ 2 ^ N := by
  have hkey := pow_addr_plus_addr_le N hN
  have hsub : Nat.log 2 N + 1 ≤ N - (2 ^ addrBits N + addrBits N) := by omega
  have hN_lt : N < 2 ^ (N - (2 ^ addrBits N + addrBits N)) :=
    calc N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self (by omega) N
      _ ≤ 2 ^ (N - (2 ^ addrBits N + addrBits N)) := Nat.pow_le_pow_right (by omega) hsub
  have hsplit : 2 ^ (2 ^ addrBits N + addrBits N) *
      2 ^ (N - (2 ^ addrBits N + addrBits N)) = 2 ^ N := by
    rw [← Nat.pow_add]; congr 1; omega
  calc 2 ^ (2 ^ addrBits N + addrBits N) * N
      ≤ 2 ^ (2 ^ addrBits N + addrBits N) *
        (2 ^ (N - (2 ^ addrBits N + addrBits N)) - 1) := by
        apply Nat.mul_le_mul_left; omega
    _ ≤ 2 ^ (2 ^ addrBits N + addrBits N) *
        2 ^ (N - (2 ^ addrBits N + addrBits N)) := by
        apply Nat.mul_le_mul_left; omega
    _ = 2 ^ N := hsplit

/-- `N ≤ 2^N` -/
private theorem n_le_pow (N : Nat) : N ≤ 2 ^ N := by
  have := @Nat.lt_pow_self N 2 (by omega); omega

/-! ### Main arithmetic inequality (proved from terms 1–4) -/

theorem lupanov_arithmetic (N : Nat) (hN : 16 ≤ N) :
    (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
      2 ^ (2 ^ addrBits N + addrBits N) + 1) * N ≤ 20 * 2 ^ N := by
  have h1 := term1 N hN
  have h2 := term2 N hN
  have h3 := term3 N hN
  have h4 := n_le_pow N
  nlinarith

/-! ### Size bound derivation (fully proved) -/

theorem lupanov_size_le (N : Nat) (hN : 16 ≤ N) (G : Nat)
    (hG : G ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
            2 ^ (2 ^ addrBits N + addrBits N)) :
    G + 1 ≤ 20 * 2 ^ N / N := by
  have hNpos : 0 < N := by omega
  apply (Nat.le_div_iff_mul_le hNpos).mpr
  calc (G + 1) * N
      ≤ (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) + 1) * N := by
        apply Nat.mul_le_mul_right; omega
    _ ≤ 20 * 2 ^ N := lupanov_arithmetic N hN

-- ════════════════════════════════════════════════════════════════
-- Section 5: Main Construction Theorem (fully proved from above)
-- ════════════════════════════════════════════════════════════════

/-- **Lupanov circuit construction**: For `N ≥ 16`, every Boolean function
    has a fan-in-2 AND/OR circuit of size `≤ 20 · 2^N / N`. -/
theorem lupanov_construction (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧ c.size ≤ 20 * 2 ^ N / N := by
  obtain ⟨G, c, heval, hG⟩ := lupanov_assembly N hN f
  exact ⟨G, c, heval, by rw [Circuit.size]; exact lupanov_size_le N hN G hG⟩

end Lupanov
