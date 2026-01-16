import Lamumu.Basic
import Lamumu.Substitution

namespace Evaluate

open Core

-- Taken from https://brandonrozek.com/blog/writing-unit-tests-lean-4/
-- By Brandon Rozek
instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case ok.ok c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)

structure EvalError where
 statement : Statement
 deriving Repr, DecidableEq

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
partial def focus (s : Statement) : Statement :=
  match s with
  | .cut p c => .cut (focusProducer p) (focusConsumer c)
  | .prim op p1 p2 c =>
    if p1.isValue && p2.isValue then
        .prim op (focusProducer p1) (focusProducer p2) (focusConsumer c)
    else if p1.isValue then
        let x := freshVarFrom [freeVarsStmt s]
        .cut (focusProducer p2)
          (.mu_tilde x (focus (.prim op p1 (.var x) c)))
    else
        let x := freshVarFrom [freeVarsStmt s]
        .cut (focusProducer p1)
          (.mu_tilde x (focus (.prim op (.var x) p2 c)))
  | .ifz p s1 s2 =>
    if p.isValue then
      .ifz (focusProducer p) (focus s1) (focus s2)
    else
      let x := freshVarFrom [freeVarsStmt s1, freeVarsStmt s2]
      .cut (focusProducer p) (.mu_tilde x (.ifz x s1 s2))

partial def focusProducer (p : Producer) : Producer :=
  match p with
  | .lit _ => p
  | .var _ => p
  | .mu c s => .mu c (focus s)

partial def focusConsumer (c : Consumer) : Consumer :=
  match c with
  | .covar _ => c
  | .mu_tilde v s => .mu_tilde v (focus s)

end

end Focus
