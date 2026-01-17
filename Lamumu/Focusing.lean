import Lamumu.Basic
import Lamumu.Binding

namespace Focus

open Core

mutual
def producerSize : Producer → Nat
  | .var _ => 0
  | .lit _ => 0
  | .mu _ s => 1 + statementSize s

def consumerSize : Consumer → Nat
  | .covar _ => 0
  | .mu_tilde _ s => 1 + statementSize s

def statementSize : Statement → Nat
  | .prim _ p1 p2 c => 1 + producerSize p1 + producerSize p2 + consumerSize c
  | .ifz p s1 s2 => 1 + producerSize p + statementSize s1 + statementSize s2
  | .cut p c => 1 + producerSize p + consumerSize c
end

theorem producerSize_lt_statementSize_cut (p : Producer) (c : Consumer) :
    producerSize p < statementSize (.cut p c) := by
  simp +arith only [statementSize]

theorem consumerSize_lt_statementSize_cut (p : Producer) (c : Consumer) :
    consumerSize c < statementSize (.cut p c) := by
  simp +arith only [statementSize]

theorem producerSize_lt_statementSize_prim_left (op : Op) (p1 p2 : Producer) (c : Consumer) :
    producerSize p1 < statementSize (.prim op p1 p2 c) := by
  simp +arith only [statementSize]

theorem producerSize_lt_statementSize_prim_right (op : Op) (p1 p2 : Producer) (c : Consumer) :
    producerSize p2 < statementSize (.prim op p1 p2 c) := by
  simp +arith only [statementSize]

theorem consumerSize_lt_statementSize_prim (op : Op) (p1 p2 : Producer) (c : Consumer) :
    consumerSize c < statementSize (.prim op p1 p2 c) := by
  simp +arith only [statementSize]

theorem producerSize_lt_statementSize_ifz (p : Producer) (s1 s2 : Statement) :
    producerSize p < statementSize (.ifz p s1 s2) := by
  simp +arith only [statementSize]

theorem statementSize_lt_statementSize_ifz_left (p : Producer) (s1 s2 : Statement) :
    statementSize s1 < statementSize (.ifz p s1 s2) := by
  simp +arith only [statementSize]

theorem statementSize_lt_statementSize_ifz_right (p : Producer) (s1 s2 : Statement) :
    statementSize s2 < statementSize (.ifz p s1 s2) := by
  simp +arith only [statementSize]

theorem statementSize_lt_producerSize_mu (c : CoVar) (s : Statement) :
    statementSize s < producerSize (.mu c s) := by
  simp +arith [producerSize]

theorem statementSize_lt_consumerSize_mu_tilde (v : Var) (s : Statement) :
    statementSize s < consumerSize (.mu_tilde v s) := by
  simp +arith [consumerSize]

mutual
  theorem producerSize_shiftVar (d c : Nat) :
      (p : Producer) → producerSize (shiftVarProducer d c p) = producerSize p
    | .var v => by
        cases v with
        | free n =>
            simp [shiftVarProducer, producerSize]
        | bound i =>
            by_cases h : c ≤ i <;> simp [shiftVarProducer, producerSize, h]
    | .lit _ => rfl
    | .mu α s => by
        simp only [shiftVarProducer, producerSize, statementSize_shiftVar d c s]

  theorem consumerSize_shiftVar (d c : Nat) :
      (cns : Consumer) → consumerSize (shiftVarConsumer d c cns) = consumerSize cns
    | .covar _ => rfl
    | .mu_tilde v s => by
        simp only [shiftVarConsumer, consumerSize, statementSize_shiftVar d (c + 1) s]

  theorem statementSize_shiftVar (d c : Nat) :
      (s : Statement) → statementSize (shiftVarStmt d c s) = statementSize s
    | .prim op p1 p2 cns => by
        simp only [shiftVarStmt, statementSize, producerSize_shiftVar d c p1,
          producerSize_shiftVar d c p2, consumerSize_shiftVar d c cns]
    | .ifz p s1 s2 => by
        simp only [shiftVarStmt, statementSize, producerSize_shiftVar d c p,
          statementSize_shiftVar d c s1, statementSize_shiftVar d c s2]
    | .cut p cns => by
        simp only [shiftVarStmt, statementSize, producerSize_shiftVar d c p,
          consumerSize_shiftVar d c cns]
end

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
