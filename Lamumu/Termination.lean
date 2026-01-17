import Lamumu.Basic
import Lamumu.Binding

namespace Termination

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

end Termination
