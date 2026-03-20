import Circ.Basic

/-! # Normal Forms — Core Definitions

This module defines Conjunctive Normal Form (CNF) and Disjunctive Normal Form (DNF)
Boolean formulas over `N` variables, together with their evaluation semantics,
complexity measures, and De Morgan negation duality.

## Main definitions

* `Literal` — a Boolean variable with a polarity flag (positive or negative)
* `CNF` — a conjunction of clauses (each clause is a disjunction of literals)
* `DNF` — a disjunction of terms (each term is a conjunction of literals)
* `CNF.complexity` — the number of clauses in a CNF formula
* `DNF.complexity` — the number of terms in a DNF formula
* `CNF.neg` / `DNF.neg` — De Morgan negation (CNF ↔ DNF)
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

/-- Negating a CNF preserves complexity. -/
theorem CNF.neg_complexity (φ : CNF N) : φ.neg.complexity = φ.complexity := by
  simp [CNF.neg, DNF.complexity, CNF.complexity, List.length_map]

/-! ## ACNF: Alternating Circuit Normal Form -/

/-- An alternating normal form tree, indexed by a `Bool` tracking the root gate type.

`ACNF N true` is an AND-rooted (or literal) tree; `ACNF N false` is OR-rooted
(or literal). Children of an AND node must be OR-rooted or literal, and vice versa.
This alternation invariant is enforced by construction: an AND node contains
`List (ACNF N false)` children, ensuring each child is OR-rooted or a literal.

Use `CNF.toACNF` / `DNF.toACNF` for direct construction from normal forms, or
`Circuit.toACNF` (via normalization) for general circuits. -/
inductive ACNF (N : Nat) : Bool → Type where
  /-- A literal leaf. Can appear at any polarity index. -/
  | lit : Literal N → ACNF N isAnd
  /-- An AND gate whose children are OR-rooted or literal. -/
  | and : List (ACNF N false) → ACNF N true
  /-- An OR gate whose children are AND-rooted or literal. -/
  | or  : List (ACNF N true) → ACNF N false

namespace ACNF

variable {N : Nat}

/-- Evaluate an ACNF tree on a bit assignment.

AND = conjunction of children (empty AND = `true`).
OR = disjunction of children (empty OR = `false`). -/
def eval : ACNF N b → BitString N → Bool
  | .lit l, x => l.eval x
  | .and children, x => evalAll children x
  | .or children, x => evalAny children x
where
  /-- Evaluate a list of children under AND (all must be true). -/
  evalAll : List (ACNF N false) → BitString N → Bool
    | [], _ => true
    | c :: cs, x => c.eval x && evalAll cs x
  /-- Evaluate a list of children under OR (at least one must be true). -/
  evalAny : List (ACNF N true) → BitString N → Bool
    | [], _ => false
    | c :: cs, x => c.eval x || evalAny cs x

/-- The depth of an ACNF tree: longest root-to-leaf path.

Literals have depth 0. An AND/OR node has depth 1 + max of children depths. -/
def depth : ACNF N b → Nat
  | .lit _ => 0
  | .and children => 1 + depthAll children
  | .or children => 1 + depthAny children
where
  /-- Maximum depth across AND children. -/
  depthAll : List (ACNF N false) → Nat
    | [] => 0
    | c :: cs => max c.depth (depthAll cs)
  /-- Maximum depth across OR children. -/
  depthAny : List (ACNF N true) → Nat
    | [] => 0
    | c :: cs => max c.depth (depthAny cs)

/-- The number of internal (AND/OR) nodes. -/
def size : ACNF N b → Nat
  | .lit _ => 0
  | .and children => 1 + sizeAll children
  | .or children => 1 + sizeAny children
where
  /-- Sum of sizes across AND children. -/
  sizeAll : List (ACNF N false) → Nat
    | [] => 0
    | c :: cs => c.size + sizeAll cs
  /-- Sum of sizes across OR children. -/
  sizeAny : List (ACNF N true) → Nat
    | [] => 0
    | c :: cs => c.size + sizeAny cs

/-- The number of literal leaves. -/
def leafCount : ACNF N b → Nat
  | .lit _ => 1
  | .and children => leafCountAll children
  | .or children => leafCountAny children
where
  /-- Sum of leaf counts across AND children. -/
  leafCountAll : List (ACNF N false) → Nat
    | [] => 0
    | c :: cs => c.leafCount + leafCountAll cs
  /-- Sum of leaf counts across OR children. -/
  leafCountAny : List (ACNF N true) → Nat
    | [] => 0
    | c :: cs => c.leafCount + leafCountAny cs

/-! ## Flattening helpers for direct circuit conversion -/

/-- For an AND parent: if child is AND, splice its children (flattening
consecutive same-op gates); otherwise wrap as a singleton. -/
def flattenForAnd : (b : Bool) × ACNF N b → List (ACNF N false)
  | ⟨_, .lit l⟩ => [.lit l]
  | ⟨_, .and children⟩ => children
  | ⟨_, .or children⟩ => [.or children]

/-- For an OR parent: if child is OR, splice its children (flattening
consecutive same-op gates); otherwise wrap as a singleton. -/
def flattenForOr : (b : Bool) × ACNF N b → List (ACNF N true)
  | ⟨_, .lit l⟩ => [.lit l]
  | ⟨_, .or children⟩ => children
  | ⟨_, .and children⟩ => [.and children]

/-- Flatten a list of sigma-typed ACNF values for an AND parent.
Each AND child is spliced in; others become singletons. -/
def flatMapForAnd : List ((b : Bool) × ACNF N b) → List (ACNF N false)
  | [] => []
  | p :: ps => flattenForAnd p ++ flatMapForAnd ps

/-- Flatten a list of sigma-typed ACNF values for an OR parent.
Each OR child is spliced in; others become singletons. -/
def flatMapForOr : List ((b : Bool) × ACNF N b) → List (ACNF N true)
  | [] => []
  | p :: ps => flattenForOr p ++ flatMapForOr ps

end ACNF

/-! ## Direct construction from CNF/DNF -/

/-- Convert a CNF formula directly to an AND-rooted ACNF tree.

A CNF `∧ᵢ (∨ⱼ lᵢⱼ)` becomes `AND [OR [lit lᵢⱼ, ...], ...]`. -/
def CNF.toACNF (φ : CNF N) : ACNF N true :=
  .and (φ.clauses.map fun clause =>
    .or (clause.map fun l => .lit l))

/-- Convert a DNF formula directly to an OR-rooted ACNF tree.

A DNF `∨ᵢ (∧ⱼ lᵢⱼ)` becomes `OR [AND [lit lᵢⱼ, ...], ...]`. -/
def DNF.toACNF (φ : DNF N) : ACNF N false :=
  .or (φ.terms.map fun term =>
    .and (term.map fun l => .lit l))
