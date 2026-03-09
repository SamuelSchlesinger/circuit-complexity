import Circ.Basic

/-- Operations in an AND/OR/NOT basis. -/
inductive AONOp where
  | and
  | or
  | not
  deriving Repr, DecidableEq

private def AONOp.eval : (op : AONOp) → (n : Nat) → (Fin n → Bool) → Bool
  | .and, n, inputs => Fin.foldl n (fun acc i => acc && inputs i) true
  | .or, n, inputs => Fin.foldl n (fun acc i => acc || inputs i) false
  | .not, n, inputs => match n, inputs with
    | _ + 1, inputs => !(inputs 0)
    | 0, _ => true

/-- AND/OR/NOT basis with unbounded fan-in for AND and OR. -/
def Basis.unboundedAON : Basis where
  Op := AONOp
  arity
    | .and => .unbounded
    | .or => .unbounded
    | .not => .exactly 1
  eval op n _ inputs := op.eval n inputs

/-- AND/OR/NOT basis with fan-in bounded by `k` for AND and OR. -/
def Basis.boundedAON (k : Nat) : Basis where
  Op := AONOp
  arity
    | .and => .upto k
    | .or => .upto k
    | .not => .exactly 1
  eval op n _ inputs := op.eval n inputs
