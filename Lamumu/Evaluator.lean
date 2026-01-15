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
def focusProducer (p : Producer) : Producer :=
  match p with
  | .lit _ => p
  | .var _ => p
  | .mu c s => .mu c (focusStatement s)

def focusStatement (s : Statement) : Statement :=
  match s with
  | .cut p c => .cut (focusProducer p) (focusConsumer c)
  | .prim op p1 p2 c => sorry
  | .ifz _ _ _ => sorry

def focusConsumer (c : Consumer) : Consumer := sorry

end

end Focus
