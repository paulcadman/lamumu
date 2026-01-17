import Lamumu.Basic

namespace Core

mutual
  def shiftVarProducer (d : Nat) (c : Nat) : Producer → Producer
    | .var v =>
        match v with
        | .free _ => .var v
        | .bound i => if c ≤ i then .var (.bound (i + d)) else .var (.bound i)
    | .lit n => .lit n
    | .mu α s => .mu α (shiftVarStmt d c s)

  def shiftVarConsumer (d : Nat) (c : Nat) : Consumer → Consumer
    | .covar α => .covar α
    | .mu_tilde v s => .mu_tilde v (shiftVarStmt d (c + 1) s)

  def shiftVarStmt (d : Nat) (c : Nat) : Statement → Statement
    | .prim op p1 p2 cns =>
        .prim op (shiftVarProducer d c p1) (shiftVarProducer d c p2) (shiftVarConsumer d c cns)
    | .ifz p s1 s2 =>
        .ifz (shiftVarProducer d c p) (shiftVarStmt d c s1) (shiftVarStmt d c s2)
    | .cut p cns =>
        .cut (shiftVarProducer d c p) (shiftVarConsumer d c cns)
end

mutual
  def shiftCoVarProducer (d : Nat) (c : Nat) : Producer → Producer
    | .var v => .var v
    | .lit n => .lit n
    | .mu α s => .mu α (shiftCoVarStmt d (c + 1) s)

  def shiftCoVarConsumer (d : Nat) (c : Nat) : Consumer → Consumer
    | .covar α =>
        match α with
        | .bound i => if c ≤ i then .covar (.bound (i + d)) else .covar (.bound i)
        | _ => .covar α
    | .mu_tilde v s => .mu_tilde v (shiftCoVarStmt d c s)

  def shiftCoVarStmt (d : Nat) (c : Nat) : Statement → Statement
    | .prim op p1 p2 cns =>
        .prim op (shiftCoVarProducer d c p1) (shiftCoVarProducer d c p2) (shiftCoVarConsumer d c cns)
    | .ifz p s1 s2 =>
        .ifz (shiftCoVarProducer d c p) (shiftCoVarStmt d c s1) (shiftCoVarStmt d c s2)
    | .cut p cns =>
        .cut (shiftCoVarProducer d c p) (shiftCoVarConsumer d c cns)
end

mutual
  def openVarProducer (k : Nat) (u : Producer) : Producer → Producer
    | .var v =>
        match v with
        | .bound i => if i = k then u else .var (.bound i)
        | .free _ => .var v
    | .lit n => .lit n
    | .mu α s => .mu α (openVarStmt k u s)

  def openVarConsumer (k : Nat) (u : Producer) : Consumer → Consumer
    | .covar α => .covar α
    | .mu_tilde v s => .mu_tilde v (openVarStmt (k + 1) u s)

  def openVarStmt (k : Nat) (u : Producer) : Statement → Statement
    | .prim op p1 p2 cns =>
        .prim op (openVarProducer k u p1) (openVarProducer k u p2) (openVarConsumer k u cns)
    | .ifz p s1 s2 =>
        .ifz (openVarProducer k u p) (openVarStmt k u s1) (openVarStmt k u s2)
    | .cut p cns =>
        .cut (openVarProducer k u p) (openVarConsumer k u cns)
end

mutual
  def openCoVarProducer (k : Nat) (u : Consumer) : Producer → Producer
    | .var v => .var v
    | .lit n => .lit n
    | .mu α s => .mu α (openCoVarStmt (k + 1) u s)

  def openCoVarConsumer (k : Nat) (u : Consumer) : Consumer → Consumer
    | .covar α =>
        match α with
        | .bound i => if i = k then u else .covar (.bound i)
        | _ => .covar α
    | .mu_tilde v s => .mu_tilde v (openCoVarStmt k u s)

  def openCoVarStmt (k : Nat) (u : Consumer) : Statement → Statement
    | .prim op p1 p2 cns =>
        .prim op (openCoVarProducer k u p1) (openCoVarProducer k u p2) (openCoVarConsumer k u cns)
    | .ifz p s1 s2 =>
        .ifz (openCoVarProducer k u p) (openCoVarStmt k u s1) (openCoVarStmt k u s2)
    | .cut p cns =>
        .cut (openCoVarProducer k u p) (openCoVarConsumer k u cns)
end

def shiftVarSubst (ps : List (Producer × Var)) : List (Producer × Var) :=
  ps.map (fun (p, v) => (shiftVarProducer 1 0 p, v))

def shiftCoVarSubst (cs : List (Consumer × CoVar)) : List (Consumer × CoVar) :=
  cs.map (fun (c, α) => (shiftCoVarConsumer 1 0 c, α))

mutual
def closeVarProducer (x : Var) (k : Nat) : Producer → Producer
  | .var v =>
      match v with
      | .free _ => if v = x then .var (.bound k) else .var v
      | .bound _ => .var v
  | .lit n => .lit n
  | .mu α s => .mu α (closeVarStmt x k s)

def closeVarConsumer (x : Var) (k : Nat) : Consumer → Consumer
  | .covar α => .covar α
  | .mu_tilde v s => .mu_tilde v (closeVarStmt x (k + 1) s)

def closeVarStmt (x : Var) (k : Nat) : Statement → Statement
  | .prim op p1 p2 c =>
      .prim op (closeVarProducer x k p1) (closeVarProducer x k p2) (closeVarConsumer x k c)
  | .ifz p s1 s2 =>
      .ifz (closeVarProducer x k p) (closeVarStmt x k s1) (closeVarStmt x k s2)
  | .cut p c =>
      .cut (closeVarProducer x k p) (closeVarConsumer x k c)
end

mutual
def closeCoVarProducer (α : CoVar) (k : Nat) : Producer → Producer
  | .var v => .var v
  | .lit n => .lit n
  | .mu β s => .mu β (closeCoVarStmt α (k + 1) s)

def closeCoVarConsumer (α : CoVar) (k : Nat) : Consumer → Consumer
  | .covar β => if β == α then .covar (.bound k) else .covar β
  | .mu_tilde v s => .mu_tilde v (closeCoVarStmt α k s)

def closeCoVarStmt (α : CoVar) (k : Nat) : Statement → Statement
  | .prim op p1 p2 c =>
      .prim op (closeCoVarProducer α k p1) (closeCoVarProducer α k p2) (closeCoVarConsumer α k c)
  | .ifz p s1 s2 =>
      .ifz (closeCoVarProducer α k p) (closeCoVarStmt α k s1) (closeCoVarStmt α k s2)
  | .cut p c =>
      .cut (closeCoVarProducer α k p) (closeCoVarConsumer α k c)
end

def closeVar (x : Var) (s : Statement) : Statement :=
  closeVarStmt x 0 s

def closeCoVar (α : CoVar) (s : Statement) : Statement :=
  closeCoVarStmt α 0 s

end Core
