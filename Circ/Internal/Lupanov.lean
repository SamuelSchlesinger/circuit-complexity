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

/-- Build a fan-in-2 gate bundled with an acyclicity proof. -/
private def mkGate2' (op : AONOp) {W : Nat} (w₀ w₁ : Fin W) (n₀ n₁ : Bool)
    (bound : Nat) (hw₀ : w₀.val < bound) (hw₁ : w₁.val < bound) :
    { g : Gate Basis.andOr2 W // ∀ k : Fin g.fanIn, (g.inputs k).val < bound } :=
  ⟨{ op := op, fanIn := 2, arityOk := rfl,
     inputs := fun i => if i.val = 0 then w₀ else w₁,
     negated := fun i => if i.val = 0 then n₀ else n₁ },
   fun k => by dsimp; split_ifs <;> assumption⟩

/-- Remap a wire from c₂'s space into the combined space. -/
private def remap₂ (N G₁ G₂ : Nat) (w : Fin (N + G₂)) : Fin (N + (G₁ + G₂ + 2)) :=
  if h : w.val < N then ⟨w.val, by omega⟩
  else ⟨w.val + G₁ + 1, by have := w.isLt; omega⟩

private lemma remap₂_val_lt (N G₁ G₂ : Nat) (w : Fin (N + G₂))
    (bound : Nat) (hb : G₁ + 1 ≤ bound) (hw : w.val < N + (bound - G₁ - 1)) :
    (remap₂ N G₁ G₂ w).val < N + bound := by
  unfold remap₂; split_ifs <;> dsimp <;> omega

private def gw (idx : Nat) {W : Nat} (g : Gate Basis.andOr2 W)
    (_ : idx < 2 := by omega) : Fin W :=
  g.inputs ⟨idx, by rw [andOr2_fanIn]; omega⟩
private def gn (idx : Nat) {W : Nat} (g : Gate Basis.andOr2 W)
    (_ : idx < 2 := by omega) : Bool :=
  g.negated ⟨idx, by rw [andOr2_fanIn]; omega⟩

-- ════════════════════════════════════════════════════════════════
-- Section 2b: Binary Circuit Composition (fully proved)
-- ════════════════════════════════════════════════════════════════

/-- Gate + acyclicity proof for the binary composition, bundled as a subtype. -/
private def binopGWP {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂)
    (i : Fin (G₁ + G₂ + 2)) :
    { g : Gate Basis.andOr2 (N + (G₁ + G₂ + 2)) //
      ∀ k : Fin g.fanIn, (g.inputs k).val < N + i.val } :=
  if h₁ : i.val < G₁ then
    let g := c₁.gates ⟨i.val, h₁⟩
    mkGate2' g.op ⟨(gw 0 g).val, by omega⟩ ⟨(gw 1 g).val, by omega⟩ (gn 0 g) (gn 1 g)
      (N + i.val)
      (show (gw 0 g).val < _ from c₁.acyclic ⟨_, h₁⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩)
      (show (gw 1 g).val < _ from c₁.acyclic ⟨_, h₁⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩)
  else if h₂ : i.val = G₁ then
    let g := c₁.outputs 0
    mkGate2' g.op ⟨(gw 0 g).val, by omega⟩ ⟨(gw 1 g).val, by omega⟩ (gn 0 g) (gn 1 g)
      (N + i.val)
      (show (gw 0 g).val < _ by have := (gw 0 g).isLt; omega)
      (show (gw 1 g).val < _ by have := (gw 1 g).isLt; omega)
  else if h₃ : i.val < G₁ + 1 + G₂ then
    let g := c₂.gates ⟨i.val - G₁ - 1, by omega⟩
    mkGate2' g.op (remap₂ N G₁ G₂ (gw 0 g)) (remap₂ N G₁ G₂ (gw 1 g)) (gn 0 g) (gn 1 g)
      (N + i.val)
      (remap₂_val_lt N G₁ G₂ (gw 0 g) i.val (by omega)
        (c₂.acyclic ⟨i.val-G₁-1, by omega⟩ ⟨0, by rw [andOr2_fanIn]; omega⟩))
      (remap₂_val_lt N G₁ G₂ (gw 1 g) i.val (by omega)
        (c₂.acyclic ⟨i.val-G₁-1, by omega⟩ ⟨1, by rw [andOr2_fanIn]; omega⟩))
  else
    let g := c₂.outputs 0
    mkGate2' g.op (remap₂ N G₁ G₂ (gw 0 g)) (remap₂ N G₁ G₂ (gw 1 g)) (gn 0 g) (gn 1 g)
      (N + i.val)
      (remap₂_val_lt N G₁ G₂ (gw 0 g) i.val (by omega)
        (show (gw 0 g).val < _ by have := (gw 0 g).isLt; omega))
      (remap₂_val_lt N G₁ G₂ (gw 1 g) i.val (by omega)
        (show (gw 1 g).val < _ by have := (gw 1 g).isLt; omega))

/-- Compose two circuits with a binary AND/OR. -/
def binopCircuit (op : AONOp) {N G₁ G₂ : Nat} [NeZero N]
    (c₁ : Circuit Basis.andOr2 N 1 G₁) (c₂ : Circuit Basis.andOr2 N 1 G₂) :
    Circuit Basis.andOr2 N 1 (G₁ + G₂ + 2) where
  gates i := (binopGWP c₁ c₂ i).val
  outputs _ :=
    { op := op, fanIn := 2, arityOk := rfl,
      inputs := fun j => if j.val = 0 then ⟨N + G₁, by omega⟩ else ⟨N + G₁ + G₂ + 1, by omega⟩,
      negated := fun _ => false }
  acyclic i k := (binopGWP c₁ c₂ i).property k

-- ════════════════════════════════════════════════════════════════
-- Section 3: Arithmetic
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

theorem dataBits_ge_two (N : Nat) (hN : 16 ≤ N) : 2 ≤ dataBits N := by
  unfold dataBits addrBits
  have : Nat.log 2 N < N := log_lt_N N hN
  have : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  omega

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

private theorem term2 (N : Nat) (hN : 16 ≤ N) :
    2 * 2 ^ addrBits N * N ≤ 2 ^ N := by
  calc 2 * 2 ^ addrBits N * N
      ≤ N * N := by apply Nat.mul_le_mul_right; exact two_mul_pow_addr_le N hN
    _ ≤ 2 ^ N := sq_le_pow N hN

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

private theorem log_le_quarter (N : Nat) (hN : 16 ≤ N) : 4 * Nat.log 2 N ≤ N := by
  have hlog4 : 4 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) (by omega)
  calc 4 * Nat.log 2 N
      ≤ 2 ^ Nat.log 2 N := pow_ge_four_mul (Nat.log 2 N) hlog4
    _ ≤ N := Nat.pow_log_le_self 2 (by omega)

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

private theorem n_le_pow (N : Nat) : N ≤ 2 ^ N := by
  have := @Nat.lt_pow_self N 2 (by omega); omega

theorem lupanov_arithmetic (N : Nat) (hN : 16 ≤ N) :
    (4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
      2 ^ (2 ^ addrBits N + addrBits N) + 1) * N ≤ 20 * 2 ^ N := by
  have h1 := term1 N hN
  have h2 := term2 N hN
  have h3 := term3 N hN
  have h4 := n_le_pow N
  nlinarith

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
-- Section 4: Circuit Construction
-- ════════════════════════════════════════════════════════════════

/-! ### Gate construction helper -/

private def mkG (W : Nat) (op : AONOp) (w0 w1 : Nat) (n0 n1 : Bool)
    (hw0 : w0 < W) (hw1 : w1 < W)
    (bound : Nat) (hb0 : w0 < bound) (hb1 : w1 < bound) :
    { g : Gate Basis.andOr2 W // ∀ j : Fin g.fanIn, (g.inputs j).val < bound } :=
  ⟨{ op := op, fanIn := 2, arityOk := rfl,
     inputs := fun j => if j.val = 0 then ⟨w0, hw0⟩ else ⟨w1, hw1⟩,
     negated := fun j => if j.val = 0 then n0 else n1 },
   fun j => by dsimp; split_ifs <;> assumption⟩

/-! ### Circuit layout -/

def szSections (kk qq : Nat) : Nat :=
  1 + (2^(qq+1) - 4) + (2^(kk+1) - 4) + 2^(2^kk) * (2^kk - 1) + 2^qq + (2^qq - 1)

lemma szSections_pos (kk qq : Nat) : 0 < szSections kk qq := by
  unfold szSections; positivity

/-! ### Section offsets (not private so they can be unfolded after `set`) -/

def oC (qq : Nat) : Nat := 1 + (2^(qq+1) - 4)
def oD (kk qq : Nat) : Nat := oC qq + (2^(kk+1) - 4)
def oE (kk qq : Nat) : Nat := oD kk qq + 2^(2^kk) * (2^kk - 1)
def oF (kk qq : Nat) : Nat := oE kk qq + 2^qq

/-! ### Power-of-2 helpers -/

private lemma pow_ge_4 (n : Nat) (hn : 2 ≤ n) : 4 ≤ 2 ^ n := by
  have : (4 : Nat) = 2 ^ 2 := by norm_num
  rw [this]; exact Nat.pow_le_pow_right (by omega) hn

private lemma pow_double (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by ring

/-! ### Minterm tree level -/

def treeLevel (j : Nat) : Nat := Nat.log 2 (j + 4) - 1

lemma treeLevel_ge_two (j : Nat) (hj : 4 ≤ j) : 2 ≤ treeLevel j := by
  unfold treeLevel
  have : 3 ≤ Nat.log 2 (j + 4) := Nat.le_log_of_pow_le (by omega) (by omega)
  omega

lemma treeLevel_lt (j n : Nat) (hj : j < 2^(n+1) - 4) (hn : 2 ≤ n) :
    treeLevel j < n := by
  unfold treeLevel
  have : j + 4 < 2^(n+1) := by have := pow_ge_4 (n+1) (by omega); omega
  have : Nat.log 2 (j + 4) < n + 1 := Nat.log_lt_of_lt_pow (by omega) this
  omega

def treeBase (l : Nat) : Nat := 2^(l+1) - 4
def treePos (j l : Nat) : Nat := j - treeBase l
def treeParentIdx (l m : Nat) : Nat := treeBase (l-1) + (m % 2^l)

lemma treeBase_le_of_level (j : Nat) (hj : 4 ≤ j) :
    treeBase (treeLevel j) ≤ j := by
  unfold treeBase treeLevel
  have h8 : 8 ≤ j + 4 := by omega
  have h3 : 3 ≤ Nat.log 2 (j + 4) := Nat.le_log_of_pow_le (by omega) (by omega)
  have hlog_sub : Nat.log 2 (j + 4) - 1 + 1 = Nat.log 2 (j + 4) := by omega
  -- 2^(log₂(j+4)) ≤ j + 4
  have hpow_le : 2 ^ Nat.log 2 (j + 4) ≤ j + 4 := Nat.pow_log_le_self 2 (by omega)
  rw [hlog_sub]; omega

lemma treeParentIdx_lt_j (l m j : Nat) (hl : 2 ≤ l)
    (hm : m = treePos j l) (hbase : treeBase l ≤ j) :
    treeParentIdx l m < j := by
  unfold treeParentIdx treeBase treePos at *
  have h4l : 4 ≤ 2^l := pow_ge_4 l hl
  have hlm1 : l - 1 + 1 = l := by omega
  have h4lm1 : 4 ≤ 2^(l-1+1) := by rw [hlm1]; exact h4l
  -- 2^(l-1) ≤ 2^l
  have hpow_le : 2^(l-1) ≤ 2^l := Nat.pow_le_pow_right (by omega) (by omega)
  -- 2^(l-1+1) = 2^l
  have hpow_eq : 2^(l-1+1) = 2^l := by rw [hlm1]
  have hmod : m % 2^l < 2^l := Nat.mod_lt _ (by positivity)
  have h2l : 2^l ≤ 2^(l+1) := Nat.pow_le_pow_right (by omega) (by omega)
  subst hm
  -- Need: 2^(l-1+1) - 4 + (j - (2^(l+1) - 4)) % 2^l < j
  rw [hpow_eq]
  omega

/-! ### Column pattern encoding -/

noncomputable def encodeCol (k : Nat) (col : Fin (2^k) → Bool) : Nat :=
  Finset.sum (Finset.univ : Finset (Fin (2^k)))
    fun j => if col j then 2^j.val else 0

private lemma sum_pow_two_lt (n : Nat) :
    Finset.sum Finset.univ (fun j : Fin n => (2 : Nat) ^ j.val) < 2 ^ n := by
  rw [Fin.sum_univ_eq_sum_range]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc Finset.sum (Finset.range n) (fun j => 2 ^ j) + 2 ^ n
        < 2 ^ n + 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

theorem encodeCol_lt (k : Nat) (col : Fin (2^k) → Bool) :
    encodeCol k col < 2^(2^k) := by
  unfold encodeCol
  calc Finset.sum Finset.univ (fun j : Fin (2^k) => if col j then 2 ^ j.val else 0)
      ≤ Finset.sum Finset.univ (fun j : Fin (2^k) => 2 ^ j.val) := by
        apply Finset.sum_le_sum; intro j _; split_ifs <;> simp [Nat.zero_le, le_refl]
    _ < 2 ^ (2^k) := sum_pow_two_lt (2^k)

noncomputable def colFun (N : Nat) (f : BitString N → Bool)
    (k q : Nat) (hkq : k + q = N) (y : Fin (2^q)) : Fin (2^k) → Bool :=
  fun a => f (fun idx =>
    if h : idx.val < k then Nat.testBit a.val idx.val
    else Nat.testBit y.val (idx.val - k))

noncomputable def colPatIdx (N : Nat) (f : BitString N → Bool)
    (k q : Nat) (hkq : k + q = N) (y : Fin (2^q)) : Nat :=
  encodeCol k (colFun N f k q hkq y)

theorem colPatIdx_lt (N : Nat) (f : BitString N → Bool)
    (k q : Nat) (hkq : k + q = N) (y : Fin (2^q)) :
    colPatIdx N f k q hkq y < 2^(2^k) :=
  encodeCol_lt k (colFun N f k q hkq y)

/-! ### Lupanov gate array -/

private noncomputable def lupanovGateArray (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) :
    (i : Fin (szSections (addrBits N) (dataBits N))) →
    { g : Gate Basis.andOr2 (N + szSections (addrBits N) (dataBits N)) //
      ∀ j : Fin g.fanIn, (g.inputs j).val < N + i.val } := by
  -- Abbreviations: we use `let` not `set` to keep definitions transparent
  let k := addrBits N
  let q := dataBits N
  let W := N + szSections k q
  let G := szSections k q
  have hkq : k + q = N := by show addrBits N + dataBits N = N; have := addr_data_sum N hN; omega
  have hk3 : 3 ≤ k := addrBits_ge_three N hN
  have hq2 : 2 ≤ q := dataBits_ge_two N hN
  have h4q : 4 ≤ 2^q := pow_ge_4 q (by omega)
  have h4k : 4 ≤ 2^k := pow_ge_4 k (by omega)
  have h4q1 : 4 ≤ 2^(q+1) := pow_ge_4 (q+1) (by omega)
  have h4k1 : 4 ≤ 2^(k+1) := pow_ge_4 (k+1) (by omega)
  have h2q1 : 2^(q+1) = 2 * 2^q := pow_double q
  have h2k1 : 2^(k+1) = 2 * 2^k := pow_double k
  have hW_pos : 0 < W := by show 0 < N + szSections k q; unfold szSections; positivity
  have hG_eq : G = oF k q + (2^q - 1) := by
    show szSections k q = oF k q + (2^q - 1)
    unfold szSections oF oE oD oC; omega
  intro i
  -- ──── Section A: constFalse (gate 0) ────
  if hiA : i.val = 0 then
    exact mkG W .and 0 0 false true (by omega) (by omega) (N + i.val) (by omega) (by omega)
  -- ──── Section B: data minterm tree ────
  else if hiB : i.val < oC q then
    let j := i.val - 1
    have hjB : j < 2^(q+1) - 4 := by unfold oC at hiB; omega
    if hjL1 : j < 4 then
      -- Level 1: AND(input[k], input[k+1])
      exact mkG W .and k (k+1) (!Nat.testBit j 0) (!Nat.testBit j 1)
        (by omega) (by omega) (N + i.val) (by omega) (by omega)
    else
      let l := treeLevel j
      let m := treePos j l
      have hl2 : 2 ≤ l := treeLevel_ge_two j (by omega)
      have hlq : l < q := treeLevel_lt j q hjB hq2
      -- Parent wire: N + 1 + treeParentIdx l m (gate in data tree)
      let pw := N + 1 + treeParentIdx l m
      let vw := k + l
      have hbase : treeBase l ≤ j := treeBase_le_of_level j (by omega)
      have hpi_lt : treeParentIdx l m < j := treeParentIdx_lt_j l m j hl2 rfl hbase
      have hpw_b : pw < N + i.val := by
        show N + 1 + treeParentIdx l m < N + i.val; omega
      have hvw_b : vw < N + i.val := by show k + l < N + i.val; omega
      -- For W bounds, chain: treeParentIdx < j = i.val - 1 < i.val < G → in W
      have hi_lt : i.val < szSections k q := i.isLt
      have hpw_W : pw < W := by
        show N + 1 + treeParentIdx l m < N + szSections k q; omega
      have hvw_W : vw < W := by show k + l < N + szSections k q; omega
      exact mkG W .and pw vw false (!Nat.testBit m l) hpw_W hvw_W (N + i.val) hpw_b hvw_b
  -- ──── Section C: address minterm tree ────
  else if hiC : i.val < oD k q then
    let j := i.val - oC q
    have hi_lt : i.val < szSections k q := i.isLt
    have hjC : j < 2^(k+1) - 4 := by
      show i.val - oC q < 2^(k+1) - 4
      have : i.val < oC q + (2^(k+1) - 4) := by unfold oD at hiC; exact hiC
      unfold oC at this ⊢; omega
    if hjL1 : j < 4 then
      exact mkG W .and 0 1 (!Nat.testBit j 0) (!Nat.testBit j 1)
        (by omega) (by omega) (N + i.val) (by omega) (by omega)
    else
      let l := treeLevel j
      let m := treePos j l
      have hl2 : 2 ≤ l := treeLevel_ge_two j (by omega)
      have hlk : l < k := treeLevel_lt j k hjC (by omega)
      let pw := N + oC q + treeParentIdx l m
      let vw := l
      have hbase : treeBase l ≤ j := treeBase_le_of_level j (by omega)
      have hpi_lt : treeParentIdx l m < j := treeParentIdx_lt_j l m j hl2 rfl hbase
      -- j < 2^(k+1) - 4, and oC q + (2^(k+1) - 4) ≤ G
      have hj_lt_G : oC q + j < G := by
        show oC q + j < szSections k q
        unfold szSections oC; omega
      have hpw_b : pw < N + i.val := by
        show N + oC q + treeParentIdx l m < N + i.val; omega
      have hvw_b : vw < N + i.val := by show l < N + i.val; omega
      have hpw_W : pw < W := by
        show N + oC q + treeParentIdx l m < N + szSections k q; omega
      have hvw_W : vw < W := by show l < N + szSections k q; omega
      exact mkG W .and pw vw false (!Nat.testBit m l) hpw_W hvw_W (N + i.val) hpw_b hvw_b
  -- ──── Section D: column library ────
  else if hiD : i.val < oE k q then
    -- Block p, position r. Block size = 2^k - 1.
    -- Linear OR chain: gate 0 ORs select(0) with select(1),
    -- gate r≥1 ORs prev with select(r+1).
    -- select(a) = addrMinterm_a if testBit(p, a) else constFalse
    let j := i.val - oD k q
    have hjD : j < 2^(2^k) * (2^k - 1) := by
      show i.val - oD k q < 2^(2^k) * (2^k - 1)
      have : i.val < oD k q + 2^(2^k) * (2^k - 1) := by unfold oE at hiD; exact hiD
      omega
    let blkSz := 2^k - 1
    have hblk_pos : 0 < blkSz := by omega
    let p := j / blkSz
    let r := j % blkSz
    have hr_lt : r < blkSz := Nat.mod_lt j hblk_pos
    -- Address minterm wire for index a: N + oC q + (2^k - 4) + a
    let amw (a : Nat) : Nat := N + oC q + (2^k - 4) + a
    let cfw : Nat := N  -- constFalse wire
    -- Simplify: r + 1 regardless of r = 0 check
    let selIdx (pos : Nat) : Nat :=
      if Nat.testBit p pos then amw pos else cfw
    let w0 : Nat := if r = 0 then selIdx 0 else N + oD k q + p * blkSz + (r - 1)
    let w1 : Nat := selIdx (r + 1)
    -- Bound proofs: all referenced wires are before the current gate
    -- Address minterms are in section C (before D)
    -- constFalse is gate 0 (before everything)
    -- previous gate in same block is at index < i
    have hamw_lt (a : Nat) (ha : a < 2^k) : amw a < N + i.val := by
      show N + oC q + (2^k - 4) + a < N + i.val
      have : oC q + (2^k - 4) + a < oD k q := by unfold oD oC; omega
      omega
    have hi_lt : i.val < szSections k q := i.isLt
    have hamw_W (a : Nat) (ha : a < 2^k) : amw a < W := by
      show N + oC q + (2^k - 4) + a < N + szSections k q
      unfold szSections oC; omega
    have hcfw_lt : cfw < N + i.val := by show N < N + i.val; omega
    have hcfw_W : cfw < W := by show N < N + szSections k q; omega
    -- selIdx bound helper
    have hsel_lt (pos : Nat) (hpos : pos < 2^k) : selIdx pos < N + i.val := by
      show (if Nat.testBit p pos then amw pos else cfw) < N + i.val
      split_ifs
      · exact hamw_lt pos hpos
      · exact hcfw_lt
    have hsel_W (pos : Nat) (hpos : pos < 2^k) : selIdx pos < W := by
      show (if Nat.testBit p pos then amw pos else cfw) < W
      split_ifs
      · exact hamw_W pos hpos
      · exact hcfw_W
    have hi_eq : oD k q + j = i.val := by omega
    have hpbr_j : blkSz * p + r = j := by
      show blkSz * (j / blkSz) + j % blkSz = j; exact Nat.div_add_mod j blkSz
    have hpbr : oD k q + p * blkSz + r = i.val := by nlinarith [mul_comm blkSz p]
    have hw0_lt : w0 < W := by
      show (if r = 0 then selIdx 0 else N + oD k q + p * blkSz + (r - 1)) < W
      split_ifs with hr0
      · exact hsel_W 0 (by omega)
      · have hi_lt := i.isLt; omega
    have hw1_lt : w1 < W := hsel_W (r + 1) (by omega)
    have hb0 : w0 < N + i.val := by
      show (if r = 0 then selIdx 0 else N + oD k q + p * blkSz + (r - 1)) < N + i.val
      split_ifs with hr0
      · exact hsel_lt 0 (by omega)
      · omega
    have hb1 : w1 < N + i.val := hsel_lt (r + 1) (by omega)
    exact mkG W .or w0 w1 false false hw0_lt hw1_lt (N + i.val) hb0 hb1
  -- ──── Section E: AND layer ────
  else if hiE : i.val < oF k q then
    let y := i.val - oE k q
    have hy : y < 2^q := by
      show i.val - oE k q < 2^q
      have : i.val < oE k q + 2^q := by unfold oF at hiE; exact hiE
      omega
    -- Data minterm: N + 1 + (2^q - 4) + y
    let dmw := N + 1 + (2^q - 4) + y
    -- Column library output for row y
    let p := colPatIdx N f k q hkq ⟨y, hy⟩
    have hp : p < 2^(2^k) := colPatIdx_lt N f k q hkq ⟨y, hy⟩
    let cw := N + oD k q + p * (2^k - 1) + (2^k - 2)
    -- dmw is in section B, which is before section E (where i lives)
    have hdmw_in_B : 1 + (2^q - 4) + y < oC q := by unfold oC; omega
    have hdmw_b : dmw < N + i.val := by
      show N + 1 + (2^q - 4) + y < N + i.val
      have : oC q ≤ oD k q := by unfold oD; omega
      have : oD k q ≤ oE k q := by unfold oE; omega
      omega
    have hdmw_W : dmw < W := by
      show N + 1 + (2^q - 4) + y < N + szSections k q
      unfold szSections at *; omega
    -- cw is the last gate of column block p (in section D, before section E)
    have hcw_in_D : p * (2^k - 1) + (2^k - 2) < 2^(2^k) * (2^k - 1) := by
      have hmul : (p + 1) * (2^k - 1) ≤ 2^(2^k) * (2^k - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hexp : p * (2^k - 1) + (2^k - 1) = (p + 1) * (2^k - 1) := by ring
      omega
    have hcw_b : cw < N + i.val := by
      show N + oD k q + p * (2^k - 1) + (2^k - 2) < N + i.val
      have hoE_le : oE k q ≤ i.val := by omega
      -- oE k q = oD k q + 2^(2^k) * (2^k - 1), and our wire < oE, so < i.val
      have : oD k q + p * (2^k - 1) + (2^k - 2) < oE k q := by
        unfold oE; omega
      omega
    have hcw_W : cw < W := by
      show N + oD k q + p * (2^k - 1) + (2^k - 2) < N + szSections k q
      have hi_lt := i.isLt; omega
    exact mkG W .and dmw cw false false hdmw_W hcw_W (N + i.val) hdmw_b hcw_b
  -- ──── Section F: OR chain ────
  else
    let r := i.val - oF k q
    have hiF : oF k q ≤ i.val := by omega
    have hr : r < 2^q - 1 := by
      show i.val - oF k q < 2^q - 1
      have : i.val < oF k q + (2^q - 1) := by rw [← hG_eq]; exact i.isLt
      omega
    let w0 : Nat := if r = 0 then N + oE k q else N + oF k q + (r - 1)
    let w1 : Nat := N + oE k q + (r + 1)
    -- oE < oF ≤ i.val, and oE + (r+1) < oE + 2^q = oF ≤ i.val
    have hoEF : oE k q < oF k q := by unfold oF; omega
    have hsz_eq : szSections k q = oF k q + (2^q - 1) := hG_eq
    have hw0_lt : w0 < W := by
      show (if r = 0 then N + oE k q else N + oF k q + (r - 1)) < N + szSections k q
      split_ifs
      · omega
      · omega
    have hw1_lt : w1 < W := by
      show N + oE k q + (r + 1) < N + szSections k q
      unfold oF at hsz_eq; omega
    have hb0 : w0 < N + i.val := by
      show (if r = 0 then N + oE k q else N + oF k q + (r - 1)) < N + i.val
      split_ifs with hr0
      · omega
      · omega
    have hb1 : w1 < N + i.val := by
      show N + oE k q + (r + 1) < N + i.val
      unfold oF at hiF; omega
    exact mkG W .or w0 w1 false false hw0_lt hw1_lt (N + i.val) hb0 hb1

private noncomputable def lupanovCircuit (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) :
    Circuit Basis.andOr2 N 1 (szSections (addrBits N) (dataBits N)) where
  gates i := (lupanovGateArray N f hN i).val
  outputs _ :=
    let lastWire := N + szSections (addrBits N) (dataBits N) - 1
    { op := .or, fanIn := 2, arityOk := rfl,
      inputs := fun _ => ⟨lastWire, by have := szSections_pos (addrBits N) (dataBits N); omega⟩,
      negated := fun _ => false }
  acyclic i k := (lupanovGateArray N f hN i).property k

/-! ### Correctness -/

private theorem lupanovCircuit_correct (N : Nat) [NeZero N]
    (f : BitString N → Bool) (hN : 16 ≤ N) (x : BitString N) :
    ((lupanovCircuit N f hN).eval x) 0 = f x := by
  sorry

private theorem szSections_le_bound (N : Nat) (hN : 16 ≤ N) :
    szSections (addrBits N) (dataBits N) ≤
      4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N + 2 ^ (2 ^ addrBits N + addrBits N) := by
  unfold szSections
  have hq1 : 1 ≤ 2 ^ dataBits N := Nat.one_le_two_pow
  have hk1 : 1 ≤ 2 ^ addrBits N := Nat.one_le_two_pow
  rw [show dataBits N + 1 = (dataBits N).succ from rfl, Nat.pow_succ]
  rw [show addrBits N + 1 = (addrBits N).succ from rfl, Nat.pow_succ]
  have hlib : 2 ^ (2 ^ addrBits N) * (2 ^ addrBits N - 1) ≤
      2 ^ (2 ^ addrBits N + addrBits N) := by
    calc 2 ^ (2 ^ addrBits N) * (2 ^ addrBits N - 1)
        ≤ 2 ^ (2 ^ addrBits N) * 2 ^ addrBits N := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ (2 ^ addrBits N + addrBits N) := by rw [← Nat.pow_add]
  omega

theorem lupanov_assembly (N : Nat) [NeZero N] (hN : 16 ≤ N)
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit Basis.andOr2 N 1 G,
      (fun x => (c.eval x) 0) = f ∧
      G ≤ 4 * 2 ^ dataBits N + 2 * 2 ^ addrBits N +
          2 ^ (2 ^ addrBits N + addrBits N) := by
  exact ⟨szSections (addrBits N) (dataBits N),
    lupanovCircuit N f hN,
    funext (lupanovCircuit_correct N f hN),
    szSections_le_bound N hN⟩

-- ════════════════════════════════════════════════════════════════
-- Section 5: Main Theorem
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
