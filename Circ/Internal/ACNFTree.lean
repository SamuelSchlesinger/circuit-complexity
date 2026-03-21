import Circ.Basic
import Circ.NF.Defs

/-! # ACNFTree: Alternating Circuit Normal Form Tree

This module defines `ACNFTree`, an alternating normal form tree indexed by a `Bool`
tracking the root gate type, together with evaluation, depth, size, leaf count,
flattening helpers, and direct construction from CNF/DNF.

## Main definitions

* `ACNFTree` — indexed inductive tree with `lit`, `and`, `or` constructors
* `ACNFTree.eval` — evaluation on a bit assignment
* `ACNFTree.depth` / `ACNFTree.size` / `ACNFTree.leafCount` — complexity measures
* `ACNFTree.flattenForAnd` / `ACNFTree.flattenForOr` — helpers for flattening
  consecutive same-op gates during circuit conversion
* `CNF.toACNFTree` / `DNF.toACNFTree` — direct construction from normal forms
-/

/-- An alternating normal form tree, indexed by a `Bool` tracking the root gate type.

`ACNFTree N true` is an AND-rooted (or literal) tree; `ACNFTree N false` is OR-rooted
(or literal). Children of an AND node must be OR-rooted or literal, and vice versa.
This alternation invariant is enforced by construction: an AND node contains
`List (ACNFTree N false)` children, ensuring each child is OR-rooted or a literal.

Use `CNF.toACNFTree` / `DNF.toACNFTree` for direct construction from normal forms, or
`Circuit.toACNFTree` (via normalization) for general circuits. -/
inductive ACNFTree (N : Nat) : Bool → Type where
  /-- A literal leaf. Can appear at any polarity index. -/
  | lit : Literal N → ACNFTree N isAnd
  /-- An AND gate whose children are OR-rooted or literal. -/
  | and : List (ACNFTree N false) → ACNFTree N true
  /-- An OR gate whose children are AND-rooted or literal. -/
  | or  : List (ACNFTree N true) → ACNFTree N false

namespace ACNFTree

variable {N : Nat}

/-- Evaluate an ACNFTree tree on a bit assignment.

AND = conjunction of children (empty AND = `true`).
OR = disjunction of children (empty OR = `false`). -/
def eval : ACNFTree N b → BitString N → Bool
  | .lit l, x => l.eval x
  | .and children, x => evalAll children x
  | .or children, x => evalAny children x
where
  /-- Evaluate a list of children under AND (all must be true). -/
  evalAll : List (ACNFTree N false) → BitString N → Bool
    | [], _ => true
    | c :: cs, x => c.eval x && evalAll cs x
  /-- Evaluate a list of children under OR (at least one must be true). -/
  evalAny : List (ACNFTree N true) → BitString N → Bool
    | [], _ => false
    | c :: cs, x => c.eval x || evalAny cs x

/-- The depth of an ACNFTree tree: longest root-to-leaf path.

Literals have depth 0. An AND/OR node has depth 1 + max of children depths. -/
def depth : ACNFTree N b → Nat
  | .lit _ => 0
  | .and children => 1 + depthList children
  | .or children => 1 + depthList children
where
  /-- Maximum depth across a list of ACNFTree children. -/
  depthList {b' : Bool} : List (ACNFTree N b') → Nat
    | [] => 0
    | c :: cs => max c.depth (depthList cs)

/-- The number of internal (AND/OR) nodes. -/
def size : ACNFTree N b → Nat
  | .lit _ => 0
  | .and children => 1 + sizeList children
  | .or children => 1 + sizeList children
where
  /-- Sum of sizes across a list of ACNFTree children. -/
  sizeList {b' : Bool} : List (ACNFTree N b') → Nat
    | [] => 0
    | c :: cs => c.size + sizeList cs

/-- The number of literal leaves. -/
def leafCount : ACNFTree N b → Nat
  | .lit _ => 1
  | .and children => leafCountList children
  | .or children => leafCountList children
where
  /-- Sum of leaf counts across a list of ACNFTree children. -/
  leafCountList {b' : Bool} : List (ACNFTree N b') → Nat
    | [] => 0
    | c :: cs => c.leafCount + leafCountList cs

/-! ## Flattening helpers for direct circuit conversion -/

/-- For an AND parent: if child is AND, splice its children (flattening
consecutive same-op gates); otherwise wrap as a singleton. -/
def flattenForAnd : (b : Bool) × ACNFTree N b → List (ACNFTree N false)
  | ⟨_, .lit l⟩ => [.lit l]
  | ⟨_, .and children⟩ => children
  | ⟨_, .or children⟩ => [.or children]

/-- For an OR parent: if child is OR, splice its children (flattening
consecutive same-op gates); otherwise wrap as a singleton. -/
def flattenForOr : (b : Bool) × ACNFTree N b → List (ACNFTree N true)
  | ⟨_, .lit l⟩ => [.lit l]
  | ⟨_, .or children⟩ => children
  | ⟨_, .and children⟩ => [.and children]

/-- Flatten a list of sigma-typed ACNFTree values for an AND parent.
Each AND child is spliced in; others become singletons. -/
def flatMapForAnd : List ((b : Bool) × ACNFTree N b) → List (ACNFTree N false)
  | [] => []
  | p :: ps => flattenForAnd p ++ flatMapForAnd ps

/-- Flatten a list of sigma-typed ACNFTree values for an OR parent.
Each OR child is spliced in; others become singletons. -/
def flatMapForOr : List ((b : Bool) × ACNFTree N b) → List (ACNFTree N true)
  | [] => []
  | p :: ps => flattenForOr p ++ flatMapForOr ps

end ACNFTree

/-! ## Direct construction from CNF/DNF -/

/-- Convert a CNF formula directly to an AND-rooted ACNFTree tree.

A CNF `∧ᵢ (∨ⱼ lᵢⱼ)` becomes `AND [OR [lit lᵢⱼ, ...], ...]`. -/
def CNF.toACNFTree (φ : CNF N) : ACNFTree N true :=
  .and (φ.clauses.map fun clause =>
    .or (clause.map fun l => .lit l))

/-- Convert a DNF formula directly to an OR-rooted ACNFTree tree.

A DNF `∨ᵢ (∧ⱼ lᵢⱼ)` becomes `OR [AND [lit lᵢⱼ, ...], ...]`. -/
def DNF.toACNFTree (φ : DNF N) : ACNFTree N false :=
  .or (φ.terms.map fun term =>
    .and (term.map fun l => .lit l))
