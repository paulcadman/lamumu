import Lean
import Lamumu.Basic
import Lamumu.Binding

open Lean

def parseSubscript (pfx : String) (s : String) : Option Nat :=
  if s.startsWith pfx then
    (s.drop pfx.length).toNat?
  else
    none

namespace Core

def cut (p : Producer) (c : Consumer) : Statement :=
  Statement.cut p c

def prim (op : Op) (p1 p2 : Producer) (c : Consumer) : Statement :=
  Statement.prim op p1 p2 c

def ifz (p : Producer) (s1 s2 : Statement) : Statement :=
  Statement.ifz p s1 s2

def lit (n : Int) : Producer :=
  Producer.lit n

scoped notation "⟨" p " | " c "⟩" => Statement.cut p c
scoped notation "+(" p1 ", " p2 "; " c ")" => Statement.prim Op.add p1 p2 c
scoped notation "*(" p1 ", " p2 "; " c ")" => Statement.prim Op.mul p1 p2 c
scoped notation "-(" p1 ", " p2 "; " c ")" => Statement.prim Op.sub p1 p2 c

scoped macro "μ " id:ident " . " body:term : term => do
  let s := id.getId.toString
  match parseSubscript "α_" s with
  | some n =>
      let lit := Syntax.mkNumLit (toString <| n)
      `(Producer.mu (CoVar.free $lit : CoVar) (closeCoVar (CoVar.free $lit : CoVar) $body))
  | none => Macro.throwUnsupported

scoped macro "μ̃ " id:ident " . " body:term : term => do
  let s := id.getId.toString
  match parseSubscript "x_" s with
  | some n =>
      let lit := Syntax.mkNumLit (toString <| n)
      `(Consumer.mu_tilde (Var.free $lit : Var) (closeVar (Var.free $lit : Var) $body))
  | none => Macro.throwUnsupported

scoped notation "⌜" n "⌝" => lit n
scoped notation "★" => Consumer.covar CoVar.star

scoped macro_rules
  | `($id:ident) => do
      let s := id.getId.toString
      match parseSubscript "α_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString <| n)
          `((CoVar.free $lit : CoVar))
      | none =>
          match parseSubscript "x_" s with
          | some n =>
              let lit := Syntax.mkNumLit (toString n)
              `((Var.free $lit : Var))
          | none => Macro.throwUnsupported

end Core

namespace Fun

def lit (n : Int) : Term :=
  Term.lit n

def ifz (t t1 t2 : Term) : Term :=
  Term.ifz t t1 t2

scoped notation "⌜" n "⌝" => lit n
scoped notation:70 t1 " + " t2 => Term.bin Op.add t1 t2
scoped notation:70 t1 " * " t2 => Term.bin Op.mul t1 t2
scoped notation:70 t1 " - " t2 => Term.bin Op.sub t1 t2

scoped syntax "let " ident " := " term " in " term : term

scoped macro_rules
  | `($id:ident) => do
      let s := id.getId.toString
      match parseSubscript "x_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString n)
          `((Var.free $lit : Var))
      | none => Macro.throwUnsupported

scoped macro_rules
  | `(let $id:ident := $assign:term in $body:term) => do
      let s := id.getId.toString
      match parseSubscript "x_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString n)
          `(Term.let (Var.free $lit) $assign $body)
      | none => Macro.throwUnsupported

end Fun
