import Circ.Basic
import Circ.AON.Defs

/-! # Normal Forms (CNF and DNF)

This file defines Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF)
Boolean formulas over `N` variables, together with their evaluation semantics,
complexity measures, and an embedding into the circuit model.

## Main definitions

* `Literal` — a Boolean variable with a polarity flag (positive or negative)
* `CNF` — a conjunction of clauses (each clause is a disjunction of literals)
* `DNF` — a disjunction of terms (each term is a conjunction of literals)
* `CNF.complexity` — the number of clauses in a CNF formula
* `DNF.complexity` — the number of terms in a DNF formula
* `CNF.toCircuit` — embed a CNF as a 2-level AND-of-ORs circuit over `Basis.unboundedAON`
* `DNF.toCircuit` — embed a DNF as a 2-level OR-of-ANDs circuit over `Basis.unboundedAON`

## Main results

* `CNF.eval_toCircuit` — the CNF circuit correctly computes the formula
* `DNF.eval_toCircuit` — the DNF circuit correctly computes the formula
* `CNF.size_toCircuit` — the CNF circuit has size `φ.complexity + 1`
* `DNF.size_toCircuit` — the DNF circuit has size `φ.complexity + 1`
* `CNF.eval_neg` — negating a CNF negates its evaluation (De Morgan duality)
* `DNF.eval_neg` — negating a DNF negates its evaluation (De Morgan duality)
-/

/-- A literal: a Boolean variable (by index) together with a polarity flag.

`polarity = true` represents the positive literal xᵢ;
`polarity = false` represents the negative literal ¬xᵢ. -/
structure Literal (N : Nat) where
  var : Fin N
  /-- `true` = positive literal (xᵢ); `false` = negative literal (¬xᵢ). -/
  polarity : Bool
  deriving DecidableEq, Repr

/-- Evaluate a literal on a bit assignment. -/
def Literal.eval (l : Literal N) (x : BitString N) : Bool :=
  if l.polarity then x l.var else !x l.var

/-- Negate a literal by flipping its polarity. -/
def Literal.neg (l : Literal N) : Literal N :=
  { l with polarity := !l.polarity }

/-- Negating a literal negates its evaluation. -/
theorem Literal.eval_neg (l : Literal N) (x : BitString N) :
    l.neg.eval x = !(l.eval x) := by
  simp [Literal.neg, Literal.eval]
  cases l.polarity <;> simp

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

/-! ## CNF -/

/--
A CNF (Conjunctive Normal Form) formula over `N` Boolean variables.

A CNF is a conjunction of clauses, where each clause is a disjunction of literals.
-/
structure CNF (N : Nat) where
  /-- The clauses of the formula. Each clause is a list of literals. -/
  clauses : List (List (Literal N))
  deriving Repr

namespace CNF

/-- A CNF formula evaluates to `true` iff every clause contains at least one
satisfied literal. -/
def eval (φ : CNF N) (x : BitString N) : Bool :=
  φ.clauses.all fun clause => clause.any fun l => l.eval x

/-- The complexity of a CNF formula is its number of clauses. -/
def complexity (φ : CNF N) : Nat := φ.clauses.length

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

/-! ## DNF -/

/--
A DNF (Disjunctive Normal Form) formula over `N` Boolean variables.

A DNF is a disjunction of terms, where each term is a conjunction of literals.
-/
structure DNF (N : Nat) where
  /-- The terms of the formula. Each term is a list of literals. -/
  terms : List (List (Literal N))
  deriving Repr

namespace DNF

/-- A DNF formula evaluates to `true` iff at least one term has all its
literals satisfied. -/
def eval (φ : DNF N) (x : BitString N) : Bool :=
  φ.terms.any fun term => term.all fun l => l.eval x

/-- The complexity of a DNF formula is its number of terms. -/
def complexity (φ : DNF N) : Nat := φ.terms.length

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

/-! ## De Morgan Negation Duality -/

/-- Negate a CNF formula by flipping all literal polarities, producing a DNF.
By De Morgan's laws, `¬(∧ᵢ ∨ⱼ lᵢⱼ) = ∨ᵢ ∧ⱼ ¬lᵢⱼ`. -/
def CNF.neg (φ : CNF N) : DNF N :=
  ⟨φ.clauses.map (fun clause => clause.map Literal.neg)⟩

/-- Negate a DNF formula by flipping all literal polarities, producing a CNF.
By De Morgan's laws, `¬(∨ᵢ ∧ⱼ lᵢⱼ) = ∧ᵢ ∨ⱼ ¬lᵢⱼ`. -/
def DNF.neg (φ : DNF N) : CNF N :=
  ⟨φ.terms.map (fun term => term.map Literal.neg)⟩

/-- Negating a CNF formula negates its evaluation (De Morgan duality). -/
theorem CNF.eval_neg (φ : CNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [CNF.neg, DNF.eval, CNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]

/-- Negating a DNF formula negates its evaluation (De Morgan duality). -/
theorem DNF.eval_neg (φ : DNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [DNF.neg, CNF.eval, DNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]
