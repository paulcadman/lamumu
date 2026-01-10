inductive Op where
  | add | mul | sub
  deriving Repr

def Op.eval (op : Op) (n m : Int) : Int :=
  match op with
  | .add => n + m
  | .mul => n * m
  | .sub => n - m

abbrev Var := Nat

inductive CoVar where
  | star : CoVar
  | idx : Nat → CoVar
  deriving Repr, BEq

namespace Fun

inductive Term where
 | var : Var → Term
 | lit : Int → Term
 | bin : Op → Term → Term → Term
 | ifz : Term → Term → Term → Term
 deriving Repr

def isValue : Term → Bool
 | .lit _ => true
 | _ => false

end Fun

namespace Core

mutual
inductive Producer where
  | var : Var → Producer
  | lit : Int → Producer
  | mu : CoVar → Statement → Producer
  deriving Repr

inductive Consumer where
  | covar : CoVar → Consumer
  deriving Repr

inductive Statement where
  | prim : Op → Producer → Producer → Consumer → Statement
  | ifz : Producer → Statement → Statement → Statement
  | cut : Producer → Consumer → Statement
  deriving Repr
end

instance : Coe CoVar Consumer :=
  ⟨Consumer.covar⟩

instance : Coe Var Producer :=
  ⟨Producer.var⟩

namespace Translate

open Fun
open Core

abbrev FreshM := StateM Nat

def freshCoVar : FreshM CoVar := do
  let n ← get
  set (n + 1)
  .idx n |> pure

def translate' : Fun.Term → FreshM Core.Producer
 | .var x => pure <| .var x
 | .lit n => pure <| .lit n
 | .bin op t1 t2 => do
   let α ← freshCoVar
   let tt1 ← translate' t1
   let tt2 ← translate' t2
   .mu α (.prim op tt1 tt2 (.covar α)) |> pure
 | .ifz cond t e => do
   let α ← freshCoVar
   let tcond ← translate' cond
   let tt ← translate' t
   let te ← translate' e
   .mu α (.ifz tcond (.cut tt (.covar α)) (.cut te (.covar α))) |> pure

def translate (t : Fun.Term) : Core.Producer := (translate' t).run 0 |>.fst

end Translate

end Core
