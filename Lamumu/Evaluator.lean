import Lamumu.Basic
import Lamumu.Binding
import Std.Tactic

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
 | .cut (.mu _ s) c => bif c.isCoValue then openCoVarStmt 0 c s |> .ok else .error ⟨s⟩
 | .cut p (.mu_tilde _ s) => if p.isValue then openVarStmt 0 p s |> .ok else .error ⟨s⟩
 | .prim op (.lit n) (.lit m) c => .cut (Op.eval op n m |> .lit) c |> .ok
 | .ifz (.lit 0) s1 _ => s1 |> .ok
 | .ifz _ _ s2 => s2 |> .ok
 | s => .error ⟨s⟩

end Evaluate

