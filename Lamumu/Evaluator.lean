import Lamumu.Basic
import Lamumu.Substitution

namespace Evaluate

open Core

structure EvalError where
 statement : Statement
 deriving Repr

def step : Statement → Except EvalError Statement
 | .cut (.mu α s) c => bif c.isCoValue then substCoVar c α s |> .ok else .error ⟨s⟩
 | .cut p (.mu_tilde x s) => if p.isValue then substVar p x s |> .ok else .error ⟨s⟩
 | .prim op (.lit n) (.lit m) c => .cut (Op.eval op n m |> .lit) c |> .ok
 | .ifz (.lit 0) s1 _ => s1 |> .ok
 | .ifz _ _ s2 => s2 |> .ok
 | s => .error ⟨s⟩

end Evaluate


namespace Focus

open Core

mutual
partial def focusProducer (p : Producer) : Producer :=
  match p with
  | .lit _ => p
  | .var _ => p
  | .mu c s => .mu c (focusStatement s)

partial def focusStatement (s : Statement) : Statement :=
  match s with
  | .cut p c => .cut (focusProducer p) (focusConsumer c)
  | .prim op p1 p2 c =>
    if p1.isValue && p2.isValue then
        .prim op (focusProducer p1) (focusProducer p2) (focusConsumer c)
    else if p1.isValue then
        let x := freshVarFrom [freeVarsStmt s]
        .cut (focusProducer p2)
          (.mu_tilde x (focusStatement (.prim op p1 (.var x) c)))
    else
        let x := freshVarFrom [freeVarsStmt s]
        .cut (focusProducer p1)
          (.mu_tilde x (focusStatement (.prim op (.var x) p2 c)))
  | .ifz p s1 s2 =>
    if p.isValue then
      .ifz (focusProducer p) (focusStatement s1) (focusStatement s2)
    else
      let x := freshVarFrom [freeVarsStmt s1, freeVarsStmt s2]
      .cut (focusProducer p) (.mu_tilde x (.ifz x s1 s2))

partial def focusConsumer (c : Consumer) : Consumer :=
  match c with
  | .covar _ => c
  | .mu_tilde v s => .mu_tilde v (focusStatement s)

end

end Focus
