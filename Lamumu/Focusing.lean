import Lamumu.Basic
import Lamumu.Binding
import Lamumu.Termination

namespace Focus

open Core
open Termination

mutual
def focus (s : Statement) : Statement :=
  match s with
  | .cut p c => .cut (focusProducer p) (focusConsumer c)
  | .prim op (.mu α s1) p2 c =>
      let x : Var := .free 0
      .cut (focusProducer (.mu α s1))
        (.mu_tilde x (focus (.prim op (.var (.bound 0)) (shiftVarProducer 1 0 p2) (shiftVarConsumer 1 0 c))))
  | .prim op p1 (.mu α s2) c =>
      let x : Var := .free 0
      .cut (focusProducer (.mu α s2))
        (.mu_tilde x (focus (.prim op (shiftVarProducer 1 0 p1) (.var (.bound 0)) (shiftVarConsumer 1 0 c))))
  | .prim op p1 p2 c =>
      .prim op (focusProducer p1) (focusProducer p2) (focusConsumer c)
  | .ifz p s1 s2 =>
    if p.isValue then
      .ifz (focusProducer p) (focus s1) (focus s2)
    else
      let x : Var := .free 0
      .cut (focusProducer p)
        (.mu_tilde x (.ifz (.var (.bound 0)) (shiftVarStmt 1 0 s1) (shiftVarStmt 1 0 s2)))
termination_by statementSize s
decreasing_by
  · exact producerSize_lt_statementSize_cut p c
  · exact consumerSize_lt_statementSize_cut p c
  · exact producerSize_lt_statementSize_prim_left op (Producer.mu α s1) p2 c
  · simp +arith only [statementSize, producerSize_shiftVar, consumerSize_shiftVar]
    exact Nat.le.intro rfl
  · exact producerSize_lt_statementSize_prim_right op p1 (Producer.mu α s2) c
  · simp +arith only [statementSize, producerSize_shiftVar, consumerSize_shiftVar]
    exact Nat.le.intro rfl
  · exact producerSize_lt_statementSize_prim_left op p1 p2 c
  · exact producerSize_lt_statementSize_prim_right op p1 p2 c
  · exact consumerSize_lt_statementSize_prim op p1 p2 c
  · exact producerSize_lt_statementSize_ifz p s1 s2
  · exact statementSize_lt_statementSize_ifz_left p s1 s2
  · exact statementSize_lt_statementSize_ifz_right p s1 s2
  · exact producerSize_lt_statementSize_ifz p s1 s2

def focusProducer (p : Producer) : Producer :=
  match p with
  | .lit _ => p
  | .var _ => p
  | .mu c s => .mu c (focus s)
termination_by producerSize p
decreasing_by
  exact statementSize_lt_producerSize_mu c s

def focusConsumer (c : Consumer) : Consumer :=
  match c with
  | .covar _ => c
  | .mu_tilde v s => .mu_tilde v (focus s)
termination_by consumerSize c
decreasing_by
  exact statementSize_lt_consumerSize_mu_tilde v s

end

end Focus
