import Circ.NF.Defs
import Circ.Internal.ACNFTree
import Circ.AON.Defs
import Mathlib.Data.Fintype.BigOperators

/-! # Internal: Normal Form Proof Machinery

This internal module contains the proof infrastructure for CNF/DNF:

* **Circuit embedding**: `CNF.toCircuit` and `DNF.toCircuit` embed normal form
  formulas as 2-level circuits over `Basis.unboundedAON`, together with
  correctness (`eval_toCircuit`) and size (`size_toCircuit`) proofs.

* **Lower bound machinery**: `DNF.flip_complexity_lb` shows that any DNF
  computing a flip-sensitive function on `N` variables needs at least `2^{N-1}`
  terms. Key lemmas include `term_mentions_all`, `full_term_unique`, and
  `card_true_of_flip_sensitive`.

The public interface re-exports the main theorems from `Circ.NF`.
-/

/-! ## Helper lemmas for toCircuit correctness -/

private lemma xor_neg_polarity_eq_eval (l : Literal N) (x : BitString N) :
    (!l.polarity).xor (x l.var) = l.eval x := by
  simp [Literal.eval]; cases l.polarity <;> simp

private lemma foldl_bor_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc || g i) false = true) ↔ (∃ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    constructor
    · intro h
      rw [Bool.or_eq_true] at h
      cases h with
      | inl h => rw [ih] at h; obtain ⟨j, hj⟩ := h; exact ⟨j.castSucc, hj⟩
      | inr h => exact ⟨Fin.last n, h⟩
    · intro ⟨i, hi⟩
      rw [Bool.or_eq_true]
      rcases Fin.lastCases (motive := fun i => (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n)
        (Or.inr rfl) (fun j => Or.inl ⟨j, rfl⟩) i with ⟨j, rfl⟩ | rfl
      · left; rw [ih]; exact ⟨j, hi⟩
      · right; exact hi

private lemma foldl_band_eq_true (n : Nat) (g : Fin n → Bool) :
    (Fin.foldl n (fun acc i => acc && g i) true = true) ↔ (∀ i : Fin n, g i = true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ_last]; constructor
    · intro h; rw [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h
      rw [ih] at h1; intro i; exact Fin.lastCases h2 (fun j => h1 j) i
    · intro h; rw [Bool.and_eq_true]
      exact ⟨(ih _).mpr (fun j => h j.castSucc), h (Fin.last n)⟩

private lemma foldl_bor_eq_list_any {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc || p (l.get i)) false = l.any p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc || p (l.get i)) false = true) ↔
      (l.any p = true) := by
    rw [foldl_bor_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨l.get i, List.get_mem l i, hi⟩
    · rintro ⟨a, ha, hp⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact ⟨i, hp⟩
  cases h1 : Fin.foldl l.length (fun acc i => acc || p (l.get i)) false <;>
    cases h2 : l.any p <;> simp_all

private lemma foldl_band_eq_list_all {α : Type} (l : List α) (p : α → Bool) :
    Fin.foldl l.length (fun acc (i : Fin l.length) => acc && p (l.get i)) true = l.all p := by
  have h_iff : (Fin.foldl l.length (fun acc i => acc && p (l.get i)) true = true) ↔
      (l.all p = true) := by
    rw [foldl_band_eq_true, List.all_eq_true]
    constructor
    · intro h a ha
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
      exact h i
    · intro h i; exact h (l.get i) (List.get_mem l i)
  cases h1 : Fin.foldl l.length (fun acc i => acc && p (l.get i)) true <;>
    cases h2 : l.all p <;> simp_all

/-! ## CNF circuit embedding -/

namespace CNF

/-- Embed a CNF formula as a 2-level AND-of-ORs circuit over `Basis.unboundedAON`.

The circuit has `φ.complexity` internal OR gates (one per clause) and a single
output AND gate. Each OR gate reads only primary input wires, with the `negated`
flag encoding literal polarity. The circuit size is `φ.complexity + 1`. -/
def toCircuit {N : Nat} [NeZero N] (φ : CNF N) :
    Circuit Basis.unboundedAON N 1 φ.complexity where
  gates i :=
    let clause := φ.clauses.get ⟨i.val, i.isLt⟩
    { op := .or
      fanIn := clause.length
      arityOk := trivial
      inputs := fun j => ⟨(clause.get j).var.val, by
        have := (clause.get j).var.isLt; omega⟩
      negated := fun j => !(clause.get j).polarity }
  outputs _ :=
    { op := .and
      fanIn := φ.complexity
      arityOk := trivial
      inputs := fun j => ⟨N + j.val, by omega⟩
      negated := fun _ => false }
  acyclic i j :=
    Nat.lt_of_lt_of_le
      ((φ.clauses.get ⟨i.val, i.isLt⟩).get ⟨j.val, j.isLt⟩).var.isLt
      (Nat.le_add_right N i.val)

private lemma wireValue_gate [NeZero N] (φ : CNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.clauses.get ⟨i.val, i.isLt⟩).any (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.clauses.get ⟨↑i, i.isLt⟩).get j).var.isLt]
  conv_lhs => arg 2; ext acc j; arg 2
              rw [xor_neg_polarity_eq_eval]
  exact foldl_bor_eq_list_any (φ.clauses.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)

/-- The circuit produced by `toCircuit` correctly computes the CNF formula. -/
theorem eval_toCircuit [NeZero N] (φ : CNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc && φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) true =
    φ.clauses.all (fun clause => clause.any fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_band_eq_list_all φ.clauses (fun clause => clause.any fun l => l.eval x)

/-- The circuit size of `toCircuit` is `φ.complexity + 1`. -/
theorem size_toCircuit [NeZero N] (φ : CNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl

end CNF

/-! ## DNF circuit embedding -/

namespace DNF

/-- Embed a DNF formula as a 2-level OR-of-ANDs circuit over `Basis.unboundedAON`.

The circuit has `φ.complexity` internal AND gates (one per term) and a single
output OR gate. Each AND gate reads only primary input wires, with the `negated`
flag encoding literal polarity. The circuit size is `φ.complexity + 1`. -/
def toCircuit {N : Nat} [NeZero N] (φ : DNF N) :
    Circuit Basis.unboundedAON N 1 φ.complexity where
  gates i :=
    let term := φ.terms.get ⟨i.val, i.isLt⟩
    { op := .and
      fanIn := term.length
      arityOk := trivial
      inputs := fun j => ⟨(term.get j).var.val, by
        have := (term.get j).var.isLt; omega⟩
      negated := fun j => !(term.get j).polarity }
  outputs _ :=
    { op := .or
      fanIn := φ.complexity
      arityOk := trivial
      inputs := fun j => ⟨N + j.val, by omega⟩
      negated := fun _ => false }
  acyclic i j :=
    Nat.lt_of_lt_of_le
      ((φ.terms.get ⟨i.val, i.isLt⟩).get ⟨j.val, j.isLt⟩).var.isLt
      (Nat.le_add_right N i.val)

private lemma wireValue_gate [NeZero N] (φ : DNF N) (x : BitString N) (i : Fin φ.complexity) :
    φ.toCircuit.wireValue x ⟨N + i.val, by omega⟩ =
      (φ.terms.get ⟨i.val, i.isLt⟩).all (fun l => l.eval x) := by
  have hge : ¬ ((⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val < N) := by simp
  rw [Circuit.wireValue_ge _ x _ hge]
  -- Normalize gate index
  have hgi : φ.toCircuit.gates ⟨(⟨N + ↑i, (by omega)⟩ : Fin (N + φ.complexity)).val - N,
    (by omega)⟩ = φ.toCircuit.gates i := by congr 1; ext; simp
  rw [hgi]
  -- Unfold gate definition
  simp only [toCircuit, Gate.eval, Basis.unboundedAON, AONOp.eval]
  -- Handle wireValue for primary inputs + xor-negation inside foldl
  conv_lhs => arg 2; ext acc j; arg 2; arg 2
              rw [Circuit.wireValue_lt _ _ _
                ((φ.terms.get ⟨↑i, i.isLt⟩).get j).var.isLt]
  conv_lhs => arg 2; ext acc j; arg 2
              rw [xor_neg_polarity_eq_eval]
  exact foldl_band_eq_list_all (φ.terms.get ⟨↑i, i.isLt⟩) (fun l => l.eval x)

/-- The circuit produced by `toCircuit` correctly computes the DNF formula. -/
theorem eval_toCircuit [NeZero N] (φ : DNF N) :
    (fun x => (φ.toCircuit.eval x) 0) = φ.eval := by
  funext x
  simp only [Circuit.eval, eval, toCircuit, Gate.eval, Basis.unboundedAON, Bool.false_xor,
    AONOp.eval]
  -- Convert struct-literal wireValue back to φ.toCircuit form for wireValue_gate
  change Fin.foldl φ.complexity
    (fun acc j => acc || φ.toCircuit.wireValue x ⟨N + j.val, by omega⟩) false =
    φ.terms.any (fun term => term.all fun l => l.eval x)
  conv_lhs => arg 2; ext acc j; arg 2; rw [wireValue_gate φ x j]
  exact foldl_bor_eq_list_any φ.terms (fun term => term.all fun l => l.eval x)

/-- The circuit size of `toCircuit` is `φ.complexity + 1`. -/
theorem size_toCircuit [NeZero N] (φ : DNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl

end DNF

/-! ## CNF/DNF Lower Bound for Flip-Sensitive Functions -/

/-- A literal that doesn't mention variable `i` evaluates the same when `i` is flipped. -/
private lemma Literal.eval_update_ne {l : Literal N} {i : Fin N} (hne : l.var ≠ i)
    (x : BitString N) (b : Bool) :
    l.eval (Function.update x i b) = l.eval x := by
  simp [Literal.eval]
  rw [Function.update_of_ne hne]

/-- If a term (conjunction of literals) doesn't mention variable `i`,
then flipping `i` doesn't change whether the term is satisfied. -/
private lemma term_eval_update {term : List (Literal N)} {i : Fin N}
    (hmiss : ∀ l ∈ term, l.var ≠ i) (x : BitString N) (b : Bool) :
    term.all (fun l => l.eval (Function.update x i b)) = term.all (fun l => l.eval x) := by
  induction term with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.all_cons]
    rw [Literal.eval_update_ne (hmiss hd List.mem_cons_self) x b]
    rw [ih (fun l hl => hmiss l (List.mem_cons_of_mem _ hl))]

/-- If `φ : DNF N` computes a flip-sensitive function, every satisfiable term
mentions all N variables. -/
theorem DNF.term_mentions_all (φ : DNF N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x)
    (term : List (Literal N)) (hterm : term ∈ φ.terms)
    (x : BitString N) (hsat : term.all (fun l => l.eval x) = true) :
    ∀ i : Fin N, ∃ l ∈ term, l.var = i := by
  intro i
  by_contra hmiss
  push_neg at hmiss
  -- hmiss : ∀ l ∈ term, l.var ≠ i
  -- Since term misses variable i, flipping i doesn't change the term
  have hsat' : term.all (fun l => l.eval (Function.update x i (!x i))) = true := by
    rw [term_eval_update hmiss]; exact hsat
  -- Both x and (flip x i) satisfy the term, so DNF is true on both
  have hx_true : φ.eval x = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat⟩
  have hx'_true : φ.eval (Function.update x i (!x i)) = true := by
    simp only [DNF.eval, List.any_eq_true]
    exact ⟨term, hterm, hsat'⟩
  -- But f flips, so f x ≠ f (flip x i)
  have := hflip x i
  rw [← hcomp, ← hcomp] at this
  rw [hx_true, hx'_true] at this
  simp at this

/-- If a term mentions all N variables, it is satisfied by at most one assignment. -/
theorem full_term_unique {term : List (Literal N)}
    (hfull : ∀ i : Fin N, ∃ l ∈ term, l.var = i)
    {x y : BitString N}
    (hx : term.all (fun l => l.eval x) = true)
    (hy : term.all (fun l => l.eval y) = true) :
    x = y := by
  funext i
  obtain ⟨l, hl_mem, hl_var⟩ := hfull i
  have hx_l : l.eval x = true := by
    rw [List.all_eq_true] at hx; exact hx l hl_mem
  have hy_l : l.eval y = true := by
    rw [List.all_eq_true] at hy; exact hy l hl_mem
  simp only [Literal.eval, hl_var] at hx_l hy_l
  split at hx_l <;> split at hy_l <;> simp_all

/-- If `f` is flip-sensitive with `N ≥ 1`, its true-set has exactly `2^{N-1}` elements. -/
theorem card_true_of_flip_sensitive {N : Nat} (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    (Finset.univ.filter (fun x => f x = true)).card = 2 ^ (N - 1) := by
  set S_true := Finset.univ.filter (fun x => f x = true)
  set S_false := Finset.univ.filter (fun x => f x = false)
  -- The involution: flip variable 0
  have hN' : 0 < N := by omega
  set flip0 : BitString N → BitString N := fun x => Function.update x ⟨0, hN'⟩ (!x ⟨0, hN'⟩)
  -- flip0 is self-inverse
  have flip0_inv : ∀ x, flip0 (flip0 x) = x := by
    intro x; ext j; simp only [flip0]
    by_cases h : j = ⟨0, hN'⟩
    · subst h; simp [Function.update_self, Bool.not_not]
    · simp [Function.update_of_ne h]
  -- flip0 maps true-set to false-set
  have flip0_tf : ∀ x, f x = true → f (flip0 x) = false := by
    intro x hx; have := hflip x ⟨0, hN'⟩; rw [hx] at this; simpa using this
  -- Bijection from S_true to S_false
  have hcard_eq : S_true.card = S_false.card := by
    apply Finset.card_bij (fun x _ => flip0 x)
    · intro x hx; simp [S_true, S_false] at hx ⊢; exact flip0_tf x hx
    · intro a₁ h₁ a₂ h₂ heq
      have := congr_arg flip0 heq
      rwa [flip0_inv, flip0_inv] at this
    · intro b hb
      refine ⟨flip0 b, ?_, flip0_inv b⟩
      simp only [S_true, S_false, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      -- f b = false, need f (flip0 b) = true
      have h1 := hflip b ⟨0, hN'⟩
      rw [hb] at h1; simpa using h1
  -- |S_true| + |S_false| = 2^N
  have hcard_total : S_true.card + S_false.card = 2 ^ N := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun x : BitString N => f x = true)
    simp only [Finset.card_univ] at h
    rw [show Fintype.card (BitString N) = 2 ^ N from by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]] at h
    convert h using 2
    simp only [S_false]
    congr 1; ext x; cases f x <;> simp
  -- 2 * S_true.card = 2^N, so S_true.card = 2^{N-1}
  have : 2 * S_true.card = 2 ^ N := by omega
  have : 2 ^ N = 2 * 2 ^ (N - 1) := by
    cases N with
    | zero => omega
    | succ n => simp [Nat.pow_succ, Nat.mul_comm]
  omega

/-- If `φ : DNF N` computes a flip-sensitive function with `N ≥ 1`,
then `2^{N-1} ≤ φ.complexity`. -/
theorem DNF.flip_complexity_lb (φ : DNF N) (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  -- Every true assignment is covered by some term, and each full term covers ≤ 1 assignment
  suffices h : (Finset.univ.filter (fun x : BitString N => f x = true)).card ≤ φ.complexity by
    rwa [card_true_of_flip_sensitive hN f hflip] at h
  -- For each true x, find a term that x satisfies
  have hfind : ∀ x : BitString N, f x = true →
      ∃ term ∈ φ.terms, term.all (fun l => l.eval x) = true := by
    intro x hx
    have : φ.eval x = true := by rw [hcomp]; exact hx
    simpa [DNF.eval, List.any_eq_true] using this
  -- Each satisfiable term mentions all variables (so is satisfied by ≤ 1 assignment)
  have huniq : ∀ term ∈ φ.terms, ∀ x₁ x₂ : BitString N,
      term.all (fun l => l.eval x₁) = true →
      term.all (fun l => l.eval x₂) = true →
      x₁ = x₂ := by
    intro term hterm x₁ x₂ h₁ h₂
    have hfull := DNF.term_mentions_all φ f hcomp hflip term hterm x₁ h₁
    exact full_term_unique hfull h₁ h₂
  -- Count: |true-set| ≤ |terms| by injection via findIdx
  -- Reformulate as card ≤ card
  rw [show φ.complexity = (Finset.range φ.complexity).card from
    (Finset.card_range φ.complexity).symm]
  apply Finset.card_le_card_of_injOn
    (fun x => φ.terms.findIdx (fun t => t.all (fun l => l.eval x)))
  · -- MapsTo: findIdx lands in range
    intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_setOf, true_and] at hx
    simp only [Finset.coe_range, Set.mem_Iio, DNF.complexity]
    rw [List.findIdx_lt_length]
    exact hfind x hx
  · -- InjOn: two true assignments with same findIdx must be equal
    intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.coe_filter, Finset.mem_univ, Set.mem_setOf, true_and] at hx₁ hx₂
    set k := φ.terms.findIdx (fun t => t.all (fun l => l.eval x₂))
    have hlt : k < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₂ hx₂
    have sat₂ : (φ.terms[k]'hlt).all (fun l => l.eval x₂) = true :=
      List.findIdx_getElem (w := hlt)
    have hlt₁ : φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁)) < φ.terms.length := by
      rw [List.findIdx_lt_length]; exact hfind x₁ hx₁
    have sat₁ : (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁).all
        (fun l => l.eval x₁) = true :=
      List.findIdx_getElem (w := hlt₁)
    have heq' : φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁)) = k := heq
    rw [show (φ.terms[φ.terms.findIdx (fun t => t.all (fun l => l.eval x₁))]'hlt₁) =
        (φ.terms[k]'hlt) from by congr 1] at sat₁
    exact huniq _ (List.getElem_mem ..) x₁ x₂ sat₁ sat₂

/-! ## Circuit maxFanIn -/

namespace Circuit

/-- Maximum fan-in across all gates (internal + output) in a single-output circuit. -/
def maxFanIn [NeZero N] (c : Circuit B N 1 G) : Nat :=
  let internal := Fin.foldl G (fun acc i => max acc (c.gates i).fanIn) 0
  max internal (c.outputs 0).fanIn

end Circuit

/-! ## Bridging: List.ofFn ↔ Fin.foldl -/

section FoldlHelpers

theorem foldl_and_init (n : Nat) (g : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc && g k) a =
    (a && Fin.foldl n (fun acc k => acc && g k) true) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and]
    rw [ih (fun k => g k.succ) (a && g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Bool.and_assoc]

theorem foldl_or_init (n : Nat) (g : Fin n → Bool) (a : Bool) :
    Fin.foldl n (fun acc k => acc || g k) a =
    (a || Fin.foldl n (fun acc k => acc || g k) false) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or]
    rw [ih (fun k => g k.succ) (a || g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Bool.or_assoc]

theorem foldl_max_init (n : Nat) (g : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => max acc (g k)) a =
    max a (Fin.foldl n (fun acc k => max acc (g k)) 0) := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_max]
    rw [ih (fun k => g k.succ) (max a (g 0))]
    rw [ih (fun k => g k.succ) (g 0)]
    simp [Nat.max_assoc]

theorem foldl_add_init (n : Nat) (g : Fin n → Nat) (a : Nat) :
    Fin.foldl n (fun acc k => acc + g k) a =
    a + Fin.foldl n (fun acc k => acc + g k) 0 := by
  induction n generalizing a with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Nat.zero_add]
    rw [ih (fun k => g k.succ) (a + g 0)]
    rw [ih (fun k => g k.succ) (g 0)]
    omega

theorem foldl_deMorgan_and (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => acc || !f k) false =
    !(Fin.foldl n (fun acc k => acc && f k) true) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.true_and, Bool.false_or]
    rw [foldl_or_init n (fun k => !(f k.succ)) (!(f 0))]
    rw [ih (fun k => f k.succ)]
    rw [foldl_and_init n (fun k => f k.succ) (f 0)]
    simp [Bool.not_and]

theorem foldl_deMorgan_or (n : Nat) (f : Fin n → Bool) :
    Fin.foldl n (fun acc k => acc && !f k) true =
    !(Fin.foldl n (fun acc k => acc || f k) false) := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    simp only [Fin.foldl_succ, Bool.false_or, Bool.true_and]
    rw [foldl_and_init n (fun k => !(f k.succ)) (!(f 0))]
    rw [ih (fun k => f k.succ)]
    rw [foldl_or_init n (fun k => f k.succ) (f 0)]
    simp [Bool.not_or]

end FoldlHelpers


/-! ## ACNFTree eval helpers for map -/

private theorem ACNFTree.evalAll_map {α : Type} (f : α → ACNFTree N false) (l : List α)
    (x : BitString N) :
    ACNFTree.eval.evalAll (l.map f) x = l.all (fun a => (f a).eval x) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map, ACNFTree.eval.evalAll, List.all_cons, ih]

private theorem ACNFTree.evalAny_map {α : Type} (f : α → ACNFTree N true) (l : List α)
    (x : BitString N) :
    ACNFTree.eval.evalAny (l.map f) x = l.any (fun a => (f a).eval x) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp only [List.map, ACNFTree.eval.evalAny, List.any_cons, ih]

/-! ## ACNFTree list lemmas -/

namespace ACNFTree

variable {N : Nat}

theorem evalAll_eq_all (cs : List (ACNFTree N false)) (x : BitString N) :
    eval.evalAll cs x = cs.all (fun c => c.eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eval.evalAll, List.all_cons, ih]

theorem evalAny_eq_any (cs : List (ACNFTree N true)) (x : BitString N) :
    eval.evalAny cs x = cs.any (fun c => c.eval x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [eval.evalAny, List.any_cons, ih]

theorem evalAll_append (l₁ l₂ : List (ACNFTree N false)) (x : BitString N) :
    eval.evalAll (l₁ ++ l₂) x = (eval.evalAll l₁ x && eval.evalAll l₂ x) := by
  induction l₁ with
  | nil => simp [eval.evalAll]
  | cons c cs ih => simp only [List.cons_append, eval.evalAll, ih, Bool.and_assoc]

theorem evalAny_append (l₁ l₂ : List (ACNFTree N true)) (x : BitString N) :
    eval.evalAny (l₁ ++ l₂) x = (eval.evalAny l₁ x || eval.evalAny l₂ x) := by
  induction l₁ with
  | nil => simp [eval.evalAny]
  | cons c cs ih => simp only [List.cons_append, eval.evalAny, ih, Bool.or_assoc]

theorem depthList_append (l₁ l₂ : List (ACNFTree N b)) :
    depth.depthList (l₁ ++ l₂) = max (depth.depthList l₁) (depth.depthList l₂) := by
  induction l₁ with
  | nil => simp [depth.depthList]
  | cons c cs ih => simp only [List.cons_append, depth.depthList, ih, Nat.max_assoc]

theorem leafCountList_append (l₁ l₂ : List (ACNFTree N b)) :
    leafCount.leafCountList (l₁ ++ l₂) =
    leafCount.leafCountList l₁ + leafCount.leafCountList l₂ := by
  induction l₁ with
  | nil => simp [leafCount.leafCountList]
  | cons c cs ih => simp only [List.cons_append, leafCount.leafCountList, ih]; omega

/-! ## Flatten correctness lemmas -/

theorem flattenForAnd_evalAll (p : (b : Bool) × ACNFTree N b) (x : BitString N) :
    eval.evalAll (flattenForAnd p) x = p.2.eval x := by
  match p with
  | ⟨_, .lit l⟩ => simp [flattenForAnd, eval.evalAll, eval]
  | ⟨_, .and children⟩ => simp [flattenForAnd, eval]
  | ⟨_, .or children⟩ => simp [flattenForAnd, eval.evalAll, eval]

theorem flattenForOr_evalAny (p : (b : Bool) × ACNFTree N b) (x : BitString N) :
    eval.evalAny (flattenForOr p) x = p.2.eval x := by
  match p with
  | ⟨_, .lit l⟩ => simp [flattenForOr, eval.evalAny, eval]
  | ⟨_, .or children⟩ => simp [flattenForOr, eval]
  | ⟨_, .and children⟩ => simp [flattenForOr, eval.evalAny, eval]

theorem flattenForAnd_depthList (p : (b : Bool) × ACNFTree N b) :
    depth.depthList (flattenForAnd p) ≤ p.2.depth := by
  match p with
  | ⟨_, .lit _⟩ => simp [flattenForAnd, depth.depthList, depth]
  | ⟨_, .and children⟩ => simp [flattenForAnd, depth]
  | ⟨_, .or children⟩ => simp [flattenForAnd, depth.depthList, depth]

theorem flattenForOr_depthList (p : (b : Bool) × ACNFTree N b) :
    depth.depthList (flattenForOr p) ≤ p.2.depth := by
  match p with
  | ⟨_, .lit _⟩ => simp [flattenForOr, depth.depthList, depth]
  | ⟨_, .or children⟩ => simp [flattenForOr, depth]
  | ⟨_, .and children⟩ => simp [flattenForOr, depth.depthList, depth]

theorem flattenForAnd_leafCountList (p : (b : Bool) × ACNFTree N b) :
    leafCount.leafCountList (flattenForAnd p) = p.2.leafCount := by
  match p with
  | ⟨_, .lit _⟩ => simp [flattenForAnd, leafCount.leafCountList, leafCount]
  | ⟨_, .and children⟩ => simp [flattenForAnd, leafCount]
  | ⟨_, .or children⟩ => simp [flattenForAnd, leafCount.leafCountList, leafCount]

theorem flattenForOr_leafCountList (p : (b : Bool) × ACNFTree N b) :
    leafCount.leafCountList (flattenForOr p) = p.2.leafCount := by
  match p with
  | ⟨_, .lit _⟩ => simp [flattenForOr, leafCount.leafCountList, leafCount]
  | ⟨_, .or children⟩ => simp [flattenForOr, leafCount]
  | ⟨_, .and children⟩ => simp [flattenForOr, leafCount.leafCountList, leafCount]

/-! ## flatMap bridge lemmas -/

theorem evalAll_flatMapForAnd (ps : List ((b : Bool) × ACNFTree N b)) (x : BitString N) :
    eval.evalAll (flatMapForAnd ps) x = ps.all (fun p => p.2.eval x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [flatMapForAnd, evalAll_append, ih, List.all_cons]
    rw [flattenForAnd_evalAll]

theorem evalAny_flatMapForOr (ps : List ((b : Bool) × ACNFTree N b)) (x : BitString N) :
    eval.evalAny (flatMapForOr ps) x = ps.any (fun p => p.2.eval x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [flatMapForOr, evalAny_append, ih, List.any_cons]
    rw [flattenForOr_evalAny]

theorem depthList_flatMapForAnd (ps : List ((b : Bool) × ACNFTree N b))
    (g : Nat) (h : ∀ p, p ∈ ps → p.2.depth ≤ g) :
    depth.depthList (flatMapForAnd ps) ≤ g := by
  induction ps with
  | nil => simp [flatMapForAnd, depth.depthList]
  | cons p ps ih =>
    simp only [flatMapForAnd, depthList_append]
    apply max_le_iff.mpr
    constructor
    · exact Nat.le_trans (flattenForAnd_depthList p) (h p (.head ps))
    · exact ih (fun q hq => h q (.tail p hq))

theorem depthList_flatMapForOr (ps : List ((b : Bool) × ACNFTree N b))
    (g : Nat) (h : ∀ p, p ∈ ps → p.2.depth ≤ g) :
    depth.depthList (flatMapForOr ps) ≤ g := by
  induction ps with
  | nil => simp [flatMapForOr, depth.depthList]
  | cons p ps ih =>
    simp only [flatMapForOr, depthList_append]
    apply max_le_iff.mpr
    constructor
    · exact Nat.le_trans (flattenForOr_depthList p) (h p (.head ps))
    · exact ih (fun q hq => h q (.tail p hq))

theorem leafCountList_flatMapForAnd_cons (p : (b : Bool) × ACNFTree N b)
    (ps : List ((b : Bool) × ACNFTree N b)) :
    leafCount.leafCountList (flatMapForAnd (p :: ps)) =
    p.2.leafCount + leafCount.leafCountList (flatMapForAnd ps) := by
  simp [flatMapForAnd, leafCountList_append, flattenForAnd_leafCountList]

theorem leafCountList_flatMapForOr_cons (p : (b : Bool) × ACNFTree N b)
    (ps : List ((b : Bool) × ACNFTree N b)) :
    leafCount.leafCountList (flatMapForOr (p :: ps)) =
    p.2.leafCount + leafCount.leafCountList (flatMapForOr ps) := by
  simp [flatMapForOr, leafCountList_append, flattenForOr_leafCountList]

end ACNFTree

/-! ## ACNFTree wrappers for CNF/DNF/Circuit conversion -/

-- Note: CNF.toACNFTree and DNF.toACNFTree are defined directly in Circ.NF.Defs.

/-- Converting a CNF to ACNFTree preserves evaluation. -/
theorem CNF.toACNFTree_eval (φ : CNF N) (x : BitString N) :
    φ.toACNFTree.eval x = φ.eval x := by
  simp only [CNF.toACNFTree, ACNFTree.eval, CNF.eval, ACNFTree.evalAll_map]
  congr 1; ext clause
  simp only [ACNFTree.eval, ACNFTree.evalAny_map, ACNFTree.eval]

/-- Converting a DNF to ACNFTree preserves evaluation. -/
theorem DNF.toACNFTree_eval (φ : DNF N) (x : BitString N) :
    φ.toACNFTree.eval x = φ.eval x := by
  simp only [DNF.toACNFTree, ACNFTree.eval, DNF.eval, ACNFTree.evalAny_map]
  congr 1; ext term
  simp only [ACNFTree.eval, ACNFTree.evalAll_map, ACNFTree.eval]

/-! ## Direct Circuit to ACNFTree conversion

Converts an unbounded-fan-in AND/OR circuit directly to a
guaranteed-alternating `ACNFTree` tree, flattening consecutive same-op gates
during the recursion (no intermediate `ACNFTree` step). -/

namespace Circuit
variable {N G : Nat} [NeZero N]

/-! ### Circuit helper lemmas -/

private theorem foldl_max_le_elem (n : Nat) (f : Fin n → Nat) (i : Fin n) :
    f i ≤ Fin.foldl n (fun acc k => max acc (f k)) 0 := by
  induction n with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    by_cases hi : (i : Nat) < n
    · exact Nat.le_trans (ih (fun j => f j.castSucc) ⟨i, hi⟩) (Nat.le_max_left _ _)
    · have : i = Fin.last n := by ext; simp [Fin.val_last]; omega
      rw [this]; exact Nat.le_max_right _ _

private theorem xor_not_xor (a b : Bool) : (!a ^^ b) = !(a ^^ b) := by
  cases a <;> cases b <;> rfl

/-- The fan-in of internal gate `i` is at most `maxFanIn`. -/
private theorem gate_fanIn_le_maxFanIn {B : Basis} (c : Circuit B N 1 G) (i : Fin G) :
    (c.gates i).fanIn ≤ maxFanIn c := by
  unfold maxFanIn
  exact Nat.le_trans (foldl_max_le_elem G (fun i => (c.gates i).fanIn) i) (Nat.le_max_left _ _)

/-- The fan-in of the output gate is at most `maxFanIn`. -/
private theorem output_fanIn_le_maxFanIn {B : Basis} (c : Circuit B N 1 G) :
    (c.outputs 0).fanIn ≤ maxFanIn c := by
  unfold maxFanIn
  exact Nat.le_max_right _ _

private theorem foldl_sum_le (n : Nat) (f : Fin n → Nat) (bound : Nat)
    (h : ∀ k, f k ≤ bound) :
    Fin.foldl n (fun acc k => acc + f k) 0 ≤ n * bound := by
  induction n with
  | zero => simp [Fin.foldl_zero]
  | succ n ih =>
    rw [Fin.foldl_succ, Nat.zero_add, foldl_add_init]
    calc f 0 + Fin.foldl n (fun acc k => acc + f k.succ) 0
        ≤ bound + n * bound :=
          Nat.add_le_add (h 0) (ih (fun k => f k.succ) (fun k => h k.succ))
      _ = (n + 1) * bound := by rw [Nat.succ_mul]; omega

/-- Convert a wire in an unbounded-fan-in AND/OR circuit directly to ACNFTree.

`pol = true` gives the wire's value; `pol = false` gives its negation.
Negations are pushed to leaves via De Morgan duality. Consecutive same-op
gates are flattened on the fly. -/
def wireToACNFTree (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) : (b : Bool) × ACNFTree N b :=
  if h : w.val < N then
    ⟨true, .lit ⟨⟨w.val, h⟩, pol⟩⟩
  else
    have hG : w.val - N < G := by omega
    let gate := c.gates ⟨w.val - N, hG⟩
    let rawChildren := List.ofFn (fun k : Fin gate.fanIn =>
      c.wireToACNFTree (gate.inputs k) (Bool.xor pol (gate.negated k)))
    match gate.op, pol with
    | .and, true  => ⟨true, .and (ACNFTree.flatMapForAnd rawChildren)⟩
    | .or, false  => ⟨true, .and (ACNFTree.flatMapForAnd rawChildren)⟩
    | .or, true   => ⟨false, .or (ACNFTree.flatMapForOr rawChildren)⟩
    | .and, false  => ⟨false, .or (ACNFTree.flatMapForOr rawChildren)⟩
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- Convert a single-output unbounded-fan-in AND/OR circuit directly to a
guaranteed-alternating ACNFTree tree. The root polarity depends on the output gate. -/
def toACNFTree (c : Circuit Basis.unboundedAON N 1 G) : (b : Bool) × ACNFTree N b :=
  let outGate := c.outputs 0
  let rawChildren := List.ofFn (fun k : Fin outGate.fanIn =>
    c.wireToACNFTree (outGate.inputs k) (Bool.xor true (outGate.negated k)))
  match outGate.op with
  | .and => ⟨true, .and (ACNFTree.flatMapForAnd rawChildren)⟩
  | .or  => ⟨false, .or (ACNFTree.flatMapForOr rawChildren)⟩

/-! ### ofFn + flatMap bridge lemmas for Fin.foldl -/

private theorem evalAll_ofFn_flatMapForAnd (n : Nat)
    (f : Fin n → (b : Bool) × ACNFTree N b) (x : BitString N) :
    ACNFTree.eval.evalAll (ACNFTree.flatMapForAnd (List.ofFn f)) x =
    (Fin.foldl n (fun acc k => acc && (f k).2.eval x) true) := by
  rw [ACNFTree.evalAll_flatMapForAnd]
  induction n with
  | zero => simp [List.ofFn_zero, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.all_cons, ih]
    conv_rhs => rw [Fin.foldl_succ]; simp only [Bool.true_and]
    exact (foldl_and_init n (fun k => (f k.succ).2.eval x)
      ((f 0).2.eval x)).symm

private theorem evalAny_ofFn_flatMapForOr (n : Nat)
    (f : Fin n → (b : Bool) × ACNFTree N b) (x : BitString N) :
    ACNFTree.eval.evalAny (ACNFTree.flatMapForOr (List.ofFn f)) x =
    (Fin.foldl n (fun acc k => acc || (f k).2.eval x) false) := by
  rw [ACNFTree.evalAny_flatMapForOr]
  induction n with
  | zero => simp [List.ofFn_zero, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, List.any_cons, ih]
    conv_rhs => rw [Fin.foldl_succ]; simp only [Bool.false_or]
    exact (foldl_or_init n (fun k => (f k.succ).2.eval x)
      ((f 0).2.eval x)).symm

private theorem depthList_ofFn_flatMapForAnd_le (n : Nat)
    (f : Fin n → (b : Bool) × ACNFTree N b) (g : Fin n → Nat)
    (h : ∀ k, (f k).2.depth ≤ g k) :
    ACNFTree.depth.depthList (ACNFTree.flatMapForAnd (List.ofFn f)) ≤
    Fin.foldl n (fun acc k => max acc (g k)) 0 := by
  apply ACNFTree.depthList_flatMapForAnd
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨k, rfl⟩ := hp
  exact Nat.le_trans (h k) (foldl_max_le_elem n g k)

private theorem depthList_ofFn_flatMapForOr_le (n : Nat)
    (f : Fin n → (b : Bool) × ACNFTree N b) (g : Fin n → Nat)
    (h : ∀ k, (f k).2.depth ≤ g k) :
    ACNFTree.depth.depthList (ACNFTree.flatMapForOr (List.ofFn f)) ≤
    Fin.foldl n (fun acc k => max acc (g k)) 0 := by
  apply ACNFTree.depthList_flatMapForOr
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨k, rfl⟩ := hp
  exact Nat.le_trans (h k) (foldl_max_le_elem n g k)

private theorem leafCountList_ofFn_flatMapForAnd (n : Nat)
    (f : Fin n → (b : Bool) × ACNFTree N b) :
    ACNFTree.leafCount.leafCountList (ACNFTree.flatMapForAnd (List.ofFn f)) =
    Fin.foldl n (fun acc k => acc + (f k).2.leafCount) 0 := by
  induction n with
  | zero => simp [List.ofFn_zero, ACNFTree.flatMapForAnd, ACNFTree.leafCount.leafCountList, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, ACNFTree.leafCountList_flatMapForAnd_cons, ih]
    conv_rhs => rw [Fin.foldl_succ]; simp only [Nat.zero_add]
    exact (foldl_add_init n (fun k => (f k.succ).2.leafCount)
      ((f 0).2.leafCount)).symm

private theorem leafCountList_ofFn_flatMapForOr (n : Nat)
    (f : Fin n → (b : Bool) × ACNFTree N b) :
    ACNFTree.leafCount.leafCountList (ACNFTree.flatMapForOr (List.ofFn f)) =
    Fin.foldl n (fun acc k => acc + (f k).2.leafCount) 0 := by
  induction n with
  | zero => simp [List.ofFn_zero, ACNFTree.flatMapForOr, ACNFTree.leafCount.leafCountList, Fin.foldl_zero]
  | succ n ih =>
    rw [List.ofFn_succ, ACNFTree.leafCountList_flatMapForOr_cons, ih]
    conv_rhs => rw [Fin.foldl_succ]; simp only [Nat.zero_add]
    exact (foldl_add_init n (fun k => (f k.succ).2.leafCount)
      ((f 0).2.leafCount)).symm

/-! ### Eval correctness -/

/-- Converting a wire to ACNFTree preserves evaluation (with polarity). -/
theorem wireToACNFTree_eval (c : Circuit Basis.unboundedAON N 1 G)
    (x : BitString N) (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNFTree w pol).2.eval x = (!pol ^^ c.wireValue x w) := by
  by_cases h : w.val < N
  · -- Primary input (w.val < N)
    rw [wireToACNFTree, dif_pos h]
    simp only [wireValue_lt c x w h, ACNFTree.eval, Literal.eval]
    cases pol <;> simp
  · -- Gate wire (w.val ≥ N)
    have hG : w.val - N < G := by omega
    rw [wireToACNFTree, dif_neg h]; dsimp only []
    conv_rhs => rw [wireValue_ge c x w h]; simp only [Gate.eval, Basis.unboundedAON]
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      dsimp only [] <;> simp only [AONOp.eval, ACNFTree.eval, Bool.true_xor,
        Bool.false_xor, Bool.not_true, Bool.not_false]
    -- AND/false: De Morgan — evalAny vs !(foldl &&)
    · have ce := fun k => wireToACNFTree_eval c x
        ((c.gates ⟨w.val - N, hG⟩).inputs k) ((c.gates ⟨w.val - N, hG⟩).negated k)
      simp_rw [xor_not_xor] at ce
      rw [evalAny_ofFn_flatMapForOr]; simp_rw [ce]; exact foldl_deMorgan_and _ _
    -- AND/true: same-op — evalAll vs foldl &&
    · have ce := fun k => wireToACNFTree_eval c x
        ((c.gates ⟨w.val - N, hG⟩).inputs k) (!(c.gates ⟨w.val - N, hG⟩).negated k)
      rw [evalAll_ofFn_flatMapForAnd]; simp_rw [ce, xor_not_xor, Bool.not_not]; rfl
    -- OR/false: De Morgan — evalAll vs !(foldl ||)
    · have ce := fun k => wireToACNFTree_eval c x
        ((c.gates ⟨w.val - N, hG⟩).inputs k) ((c.gates ⟨w.val - N, hG⟩).negated k)
      simp_rw [xor_not_xor] at ce
      rw [evalAll_ofFn_flatMapForAnd]; simp_rw [ce]; exact foldl_deMorgan_or _ _
    -- OR/true: same-op — evalAny vs foldl ||
    · have ce := fun k => wireToACNFTree_eval c x
        ((c.gates ⟨w.val - N, hG⟩).inputs k) (!(c.gates ⟨w.val - N, hG⟩).negated k)
      rw [evalAny_ofFn_flatMapForOr]; simp_rw [ce, xor_not_xor, Bool.not_not]; rfl
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- Converting a circuit to ACNFTree preserves evaluation. -/
theorem toACNFTree_eval (c : Circuit Basis.unboundedAON N 1 G) (x : BitString N) :
    (c.toACNFTree).2.eval x = (c.eval x) 0 := by
  simp only [toACNFTree, eval, Gate.eval, Basis.unboundedAON]
  rcases hop : (c.outputs 0).op with _ | _
  · simp only [AONOp.eval, ACNFTree.eval]
    rw [evalAll_ofFn_flatMapForAnd]; simp_rw [wireToACNFTree_eval, Bool.true_xor, Bool.not_not]; rfl
  · simp only [AONOp.eval, ACNFTree.eval]
    rw [evalAny_ofFn_flatMapForOr]; simp_rw [wireToACNFTree_eval, Bool.true_xor, Bool.not_not]; rfl

/-! ### Depth bound -/

/-- The ACNFTree for a wire has depth at most the wire's depth. -/
theorem wireToACNFTree_depth_le (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNFTree w pol).2.depth ≤ c.wireDepth w := by
  by_cases h : w.val < N
  · rw [wireToACNFTree, dif_pos h]; simp [inputWireDepth c w h, ACNFTree.depth]
  · have hG : w.val - N < G := by omega
    rw [wireToACNFTree, dif_neg h]; dsimp only []
    conv_rhs => rw [gateWireDepth c w h]
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      dsimp only [] <;> simp only [ACNFTree.depth]
    all_goals (
      apply Nat.add_le_add_left
      first
      | exact depthList_ofFn_flatMapForAnd_le _ _ _ fun k =>
          wireToACNFTree_depth_le c ((c.gates ⟨w.val - N, hG⟩).inputs k) _
      | exact depthList_ofFn_flatMapForOr_le _ _ _ fun k =>
          wireToACNFTree_depth_le c ((c.gates ⟨w.val - N, hG⟩).inputs k) _)
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- The ACNFTree depth is at most the circuit depth. -/
theorem toACNFTree_depth_le (c : Circuit Basis.unboundedAON N 1 G) :
    (c.toACNFTree).2.depth ≤ c.depth := by
  simp only [toACNFTree, depth]
  rcases (c.outputs 0).op with _ | _ <;>
    simp only [ACNFTree.depth]
  · exact Nat.add_le_add_left
      (depthList_ofFn_flatMapForAnd_le _ _ _ fun k =>
        wireToACNFTree_depth_le c ((c.outputs 0).inputs k) _) 1
  · exact Nat.add_le_add_left
      (depthList_ofFn_flatMapForOr_le _ _ _ fun k =>
        wireToACNFTree_depth_le c ((c.outputs 0).inputs k) _) 1

/-! ### Leaf count bound -/

/-- The ACNFTree for a wire has at most `maxFanIn ^ wireDepth` leaves. -/
theorem wireToACNFTree_leafCount_le (c : Circuit Basis.unboundedAON N 1 G)
    (w : Fin (N + G)) (pol : Bool) :
    (c.wireToACNFTree w pol).2.leafCount ≤ c.maxFanIn ^ c.wireDepth w := by
  by_cases h : w.val < N
  · rw [wireToACNFTree, dif_pos h]; simp [inputWireDepth c w h, ACNFTree.leafCount]
  · have hG : w.val - N < G := by omega
    rw [wireToACNFTree, dif_neg h]; dsimp only []
    conv_rhs => rw [gateWireDepth c w h]
    have lc_ih : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
        (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
          (pol ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).2.leafCount ≤
        c.maxFanIn ^ c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k) :=
      fun k => wireToACNFTree_leafCount_le c _ _
    rcases hop : (c.gates ⟨w.val - N, hG⟩).op with _ | _ <;> rcases pol with _ | _ <;>
      dsimp only [] <;> simp only [ACNFTree.leafCount]
    all_goals (
      first
      | rw [leafCountList_ofFn_flatMapForAnd]
      | rw [leafCountList_ofFn_flatMapForOr]
      set D := Fin.foldl (c.gates ⟨w.val - N, hG⟩).fanIn
            (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k))) 0
      have hD : ∀ k, c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs k) ≤ D :=
        fun k => foldl_max_le_elem _
          (fun j => c.wireDepth ((c.gates ⟨w.val - N, hG⟩).inputs j)) k
      by_cases hM : c.maxFanIn = 0
      · have : (c.gates ⟨w.val - N, hG⟩).fanIn = 0 := by
          have := gate_fanIn_le_maxFanIn c ⟨w.val - N, hG⟩; omega
        simp [this, Fin.foldl_zero]
      · have hM_pos : 0 < c.maxFanIn := Nat.pos_of_ne_zero hM
        have hbound : ∀ k : Fin (c.gates ⟨w.val - N, hG⟩).fanIn,
            (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
              (_ ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).2.leafCount ≤
            c.maxFanIn ^ D :=
          fun k => Nat.le_trans (lc_ih k) (Nat.pow_le_pow_right hM_pos (hD k))
        calc Fin.foldl _ (fun acc k => acc +
                (c.wireToACNFTree ((c.gates ⟨w.val - N, hG⟩).inputs k)
                  (_ ^^ (c.gates ⟨w.val - N, hG⟩).negated k)).2.leafCount) 0
            ≤ _ * c.maxFanIn ^ D := foldl_sum_le _ _ _ hbound
          _ ≤ c.maxFanIn * c.maxFanIn ^ D :=
              Nat.mul_le_mul_right _ (gate_fanIn_le_maxFanIn c ⟨w.val - N, hG⟩)
          _ = c.maxFanIn ^ (D + 1) := (pow_succ' c.maxFanIn D).symm
          _ = c.maxFanIn ^ (1 + D) := by congr 1; omega)
termination_by w.val
decreasing_by
  all_goals (
    have hacyc := c.acyclic ⟨w.val - N, by omega⟩ k
    have : (⟨w.val - N, by omega⟩ : Fin G).val = w.val - N := rfl
    omega)

/-- The ACNFTree leaf count is at most `maxFanIn ^ depth`. -/
theorem toACNFTree_leafCount_le (c : Circuit Basis.unboundedAON N 1 G) :
    (c.toACNFTree).2.leafCount ≤ c.maxFanIn ^ c.depth := by
  simp only [toACNFTree, depth]
  rcases hop : (c.outputs 0).op with _ | _ <;>
    (simp only []; simp only [ACNFTree.leafCount])
  all_goals (
    first
    | rw [leafCountList_ofFn_flatMapForAnd]
    | rw [leafCountList_ofFn_flatMapForOr]
    set D := Fin.foldl (c.outputs 0).fanIn
          (fun acc k => max acc (c.wireDepth ((c.outputs 0).inputs k))) 0
    have hD : ∀ k, c.wireDepth ((c.outputs 0).inputs k) ≤ D :=
      fun k => foldl_max_le_elem _
        (fun j => c.wireDepth ((c.outputs 0).inputs j)) k
    by_cases hM : c.maxFanIn = 0
    · have : (c.outputs 0).fanIn = 0 := by
        have := output_fanIn_le_maxFanIn c; omega
      simp [this, Fin.foldl_zero]
    · have hM_pos : 0 < c.maxFanIn := Nat.pos_of_ne_zero hM
      have hbound : ∀ k : Fin (c.outputs 0).fanIn,
          (c.wireToACNFTree ((c.outputs 0).inputs k)
            (true ^^ (c.outputs 0).negated k)).2.leafCount ≤
          c.maxFanIn ^ D :=
        fun k => Nat.le_trans (wireToACNFTree_leafCount_le c _ _)
          (Nat.pow_le_pow_right hM_pos (hD k))
      calc Fin.foldl _ (fun acc k => acc +
              (c.wireToACNFTree ((c.outputs 0).inputs k)
                (true ^^ (c.outputs 0).negated k)).2.leafCount) 0
          ≤ _ * c.maxFanIn ^ D := foldl_sum_le _ _ _ hbound
        _ ≤ c.maxFanIn * c.maxFanIn ^ D :=
            Nat.mul_le_mul_right _ (output_fanIn_le_maxFanIn c)
        _ = c.maxFanIn ^ (D + 1) := (pow_succ' c.maxFanIn D).symm
        _ = c.maxFanIn ^ (1 + D) := by congr 1; omega)

end Circuit
