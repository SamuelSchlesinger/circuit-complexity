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

end CNF

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

end DNF
