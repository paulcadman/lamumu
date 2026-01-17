inductive Op where
  | add | mul | sub
  deriving Repr, DecidableEq

def Op.eval (op : Op) (n m : Int) : Int :=
  match op with
  | .add => n + m
  | .mul => n * m
  | .sub => n - m

inductive Var where
  | free : Nat → Var
  | bound : Nat → Var
  deriving Repr, DecidableEq

inductive CoVar where
  | star : CoVar
  | free : Nat → CoVar
  | bound : Nat → CoVar
  deriving Repr, DecidableEq

instance : Coe Nat Var :=
  ⟨Var.free⟩

instance : Coe Nat CoVar :=
  ⟨CoVar.free⟩

namespace Core

mutual
inductive Producer where
  | var : Var → Producer
  | lit : Int → Producer
  | mu : CoVar → Statement → Producer
  deriving Repr, DecidableEq

inductive Consumer where
  | covar : CoVar → Consumer
  | mu_tilde : Var → Statement → Consumer
  deriving Repr, DecidableEq

inductive Statement where
  | prim : Op → Producer → Producer → Consumer → Statement
  | ifz : Producer → Statement → Statement → Statement
  | cut : Producer → Consumer → Statement
  deriving Repr, DecidableEq
end

def Producer.isValue : Producer → Bool
  | .lit _ => True
  | .var _ => True
  | .mu _ _ => False

def Consumer.isCoValue : Consumer → Bool
  | .mu_tilde _ _ => True
  | .covar _ => True

instance : Coe CoVar Consumer :=
  ⟨Consumer.covar⟩

instance : Coe Var Producer :=
  ⟨Producer.var⟩

end Core

namespace Fun

inductive Term where
 | var : Var → Term
 | lit : Int → Term
 | bin : Op → Term → Term → Term
 | ifz : Term → Term → Term → Term
 | let : Var → Term → Term → Term
 deriving Repr

def isValue : Term → Bool
 | .lit _ => true
 | _ => false


instance : Coe Var Term :=
  ⟨Term.var⟩

end Fun
