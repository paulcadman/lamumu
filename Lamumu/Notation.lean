import Lean
import Lamumu.Basic
import Lamumu.Binding

open Lean

def parseSubscript (pfx : String) (s : String) : Option Nat :=
  if s.startsWith pfx then
    (s.drop pfx.length).toNat?
  else
    none

namespace Lean.Parser

declare_syntax_cat coreProducer
declare_syntax_cat coreConsumer
declare_syntax_cat coreStatement
declare_syntax_cat coreOp

syntax num : coreProducer
syntax "-" num : coreProducer
syntax ident : coreProducer
syntax "mu " ident " . " coreStatement : coreProducer
syntax "μ " ident " . " coreStatement : coreProducer

syntax ident : coreConsumer

syntax "add" : coreOp
syntax "mul" : coreOp
syntax "sub" : coreOp
syntax "+" : coreOp
syntax "*" : coreOp
syntax "-" : coreOp

syntax "⟨" coreProducer " | " coreConsumer "⟩" : coreStatement
syntax "<" coreProducer " | " coreConsumer ">" : coreStatement
syntax "+(" coreProducer ", " coreProducer "; " coreConsumer ")" : coreStatement
syntax "*(" coreProducer ", " coreProducer "; " coreConsumer ")" : coreStatement
syntax "-(" coreProducer ", " coreProducer "; " coreConsumer ")" : coreStatement

end Lean.Parser

macro_rules
  | `($id:ident) => do
      let s := id.getId.toString
      match parseSubscript "α_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString <| n)
          return ← `((CoVar.free $lit : CoVar))
      | none =>
          match parseSubscript "x_" s with
          | some n =>
              let lit := Syntax.mkNumLit (toString n)
              return ← `((Var.free $lit : Var))
          | none => Macro.throwUnsupported

namespace Core

def cut (p : Producer) (c : Consumer) : Statement :=
  Statement.cut p c

def prim (op : Op) (p1 p2 : Producer) (c : Consumer) : Statement :=
  Statement.prim op p1 p2 c

def ifz (p : Producer) (s1 s2 : Statement) : Statement :=
  Statement.ifz p s1 s2

def lit (n : Int) : Producer :=
  Producer.lit n

notation "⟨" p " | " c "⟩" => Statement.cut p c
syntax "+(" term ", " term "; " term ")" : term
syntax "*(" term ", " term "; " term ")" : term
syntax "-(" term ", " term "; " term ")" : term
macro_rules
  | `(+( $p1:term, $p2:term; $c:term)) => `(Statement.prim Op.add $p1 $p2 $c)
  | `(*( $p1:term, $p2:term; $c:term)) => `(Statement.prim Op.mul $p1 $p2 $c)
  | `(-( $p1:term, $p2:term; $c:term)) => `(Statement.prim Op.sub $p1 $p2 $c)

syntax "mu " ident " . " term : term
syntax "μ " ident " . " term : term
macro_rules
  | `(mu $id:ident . $body:term) => do
      let s := id.getId.toString
      match parseSubscript "α_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString <| n)
          `(Producer.mu (CoVar.free $lit : CoVar) (closeCoVar (CoVar.free $lit : CoVar) $body))
      | none => Macro.throwUnsupported
  | `(μ $id:ident . $body:term) => do
      let s := id.getId.toString
      match parseSubscript "α_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString <| n)
          `(Producer.mu (CoVar.free $lit : CoVar) (closeCoVar (CoVar.free $lit : CoVar) $body))
      | none => Macro.throwUnsupported

syntax "μ̃ " ident " . " term : term
macro_rules
  | `(μ̃ $id:ident . $body:term) => do
      let s := id.getId.toString
      match parseSubscript "x_" s with
      | some n =>
          let lit := Syntax.mkNumLit (toString <| n)
          `(Consumer.mu_tilde (Var.free $lit : Var) (closeVar (Var.free $lit : Var) $body))
      | none => Macro.throwUnsupported

notation "μ[" α "] " s => Producer.mu α s
notation "mu[" α "] " s => Producer.mu α s
notation "⌜" n "⌝" => lit n
notation "★" => Consumer.covar CoVar.star

end Core
