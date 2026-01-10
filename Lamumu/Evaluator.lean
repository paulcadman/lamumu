import Lamumu.Basic
import Lamumu.Substitution

namespace Evaluate

open Core

def step : Statement → Option Statement
 | .cut (.mu α s) c => substCoVar c α s |> some
 | .prim op (.lit n) (.lit m) c => .cut (Op.eval op n m |> .lit) c |> some
 | .ifz (.lit 0) s1 _ => s1 |> some
 | .ifz _ _ s2 => s2 |> some
 | _ => none

end Evaluate
