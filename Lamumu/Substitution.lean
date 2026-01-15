import Lamumu.Basic

namespace Core

def unionLists (xs : List (List Nat)) : List Nat :=
  xs.foldl (· ++ ·) []

def removeAll (xs : List Nat) (n : Nat) : List Nat :=
  xs.filter (fun m => m != n)

def maxList (xs : List Nat) : Nat :=
  xs.foldl Nat.max 0

def freshFrom (used : List Nat) : Nat :=
  match used with
  | [] => 0
  | _ => maxList used + 1


mutual
  def freeVarsProducer : Producer -> List Var
    | .var v => [v]
    | .lit _ => []
    | .mu _ s => freeVarsStmt s

  def freeVarsConsumer : Consumer -> List Var
    | .covar _ => []
    | .mu_tilde v s => removeAll (freeVarsStmt s) v

  def freeVarsStmt : Statement -> List Var
    | .prim _ p1 p2 c => freeVarsProducer p1 ++ freeVarsProducer p2 ++ freeVarsConsumer c
    | .ifz p s1 s2 => freeVarsProducer p ++ freeVarsStmt s1 ++ freeVarsStmt s2
    | .cut p c => freeVarsProducer p ++ freeVarsConsumer c
end

mutual
  def freeCoVarsProducer : Producer -> List Nat
    | .var _ => []
    | .lit _ => []
    | .mu (.idx n) s => removeAll (freeCoVarsStmt s) n
    | .mu .star _ => []

  def freeCoVarsConsumer : Consumer -> List Nat
    | .covar (.idx n) => [n]
    | .covar .star => []
    | .mu_tilde _ s => freeCoVarsStmt s

  def freeCoVarsStmt : Statement -> List Nat
    | .prim _ p1 p2 c => freeCoVarsProducer p1 ++ freeCoVarsProducer p2 ++ freeCoVarsConsumer c
    | .ifz p s1 s2 => freeCoVarsProducer p ++ freeCoVarsStmt s1 ++ freeCoVarsStmt s2
    | .cut p c => freeCoVarsProducer p ++ freeCoVarsConsumer c
end

def freshVarFrom (xs : List (List Var)) : Var :=
  freshFrom (unionLists xs)

def freshCoVarFrom (xs : List (List Nat)) : CoVar :=
  freshFrom (unionLists xs) |> .idx

def freeCoVarsSubst (ps : List (Producer × Var)) : List Nat :=
  ps.foldl (fun acc (p, _) => acc ++ freeCoVarsProducer p) []

def freeCoVarsCoSubst (cs : List (Consumer × CoVar)) : List Nat :=
  cs.foldl (fun acc (c, _) => acc ++ freeCoVarsConsumer c) []

def freeVarsSubst (ps : List (Producer × Var)) : List Var :=
  ps.foldl (fun acc (p, _) => acc ++ freeVarsProducer p) []

def freeVarsCoSubst (cs : List (Consumer × CoVar)) : List Var :=
  cs.foldl (fun acc (c, _) => acc ++ freeVarsConsumer c) []

def lookupVar (ps : List (Producer × Var)) (v : Var) : Option Producer :=
  match ps.find? (fun (_, v') => v' = v) with
  | some (p, _) => some p
  | none => none

def lookupCoVar (cs : List (Consumer × CoVar)) (α : CoVar) : Option Consumer :=
  match cs.find? (fun (_, α') => α' == α) with
  | some (c, _) => some c
  | none => none

-- These are paritial because the termination checker fails
mutual
  partial def substSimProducer (ps : List (Producer × Var)) (cs : List (Consumer × CoVar)) :
      Producer -> Producer
    | .var v =>
        match lookupVar ps v with
        | some p => p
        | none => .var v
    | .lit n => .lit n
    | .mu α s =>
        let avoid := freeCoVarsStmt s ++ freeCoVarsSubst ps ++ freeCoVarsCoSubst cs
        let α' := freshCoVarFrom [avoid]
        let s' := substSimStmt [] [(.covar α', α)] s
        .mu α' (substSimStmt ps cs s')

  partial def substSimConsumer (ps : List (Producer × Var)) (cs : List (Consumer × CoVar)) :
      Consumer -> Consumer
    | .covar α =>
        match lookupCoVar cs α with
        | some c => c
        | none => .covar α
    | .mu_tilde v s =>
        let avoid := [freeVarsStmt s, ps.map (fun (_, v') => v'), freeVarsSubst ps, freeVarsCoSubst cs]
        let v' := freshVarFrom avoid
        let s' := substSimStmt [(.var v', v)] [] s
        .mu_tilde v' (substSimStmt ps cs s')

  partial def substSimStmt (ps : List (Producer × Var)) (cs : List (Consumer × CoVar)) :
      Statement -> Statement
    | .prim op p1 p2 c =>
        .prim op (substSimProducer ps cs p1) (substSimProducer ps cs p2) (substSimConsumer ps cs c)
    | .ifz p s1 s2 =>
        .ifz (substSimProducer ps cs p) (substSimStmt ps cs s1) (substSimStmt ps cs s2)
    | .cut p c =>
        .cut (substSimProducer ps cs p) (substSimConsumer ps cs c)
end

def substSim (ps : List (Producer × Var)) (cs : List (Consumer × CoVar)) (s : Statement) :
    Statement :=
  substSimStmt ps cs s

def substVar (p : Producer) (v : Var) (s : Statement) : Statement :=
  substSimStmt [(p, v)] [] s

def substCoVar (c : Consumer) (α : CoVar) (s : Statement) : Statement :=
  substSimStmt [] [(c, α)] s

end Core
