import Lamumu.Basic
import Lamumu.Notation

namespace Core

open Std

def ppVar : Var → String
  | .free n => s!"x_{n}"
  | .bound n => s!"x_{n}"

def ppCoVar : CoVar → String
  | .star => "★"
  | .free n => s!"α_{n}"
  | .bound n => s!"α_{n}"

def ppOp : Op -> String
  | .add => "+"
  | .mul => "*"
  | .sub => "-"

mutual
  def ppProducerCtx (vctx : List Var) (cctx : List CoVar) : Producer -> String
    | .var v =>
        match v with
        | .bound i => ppVar (vctx.getD i (.free 0))
        | .free _ => ppVar v
    | .lit n => s!"⌜{n}⌝"
    | .mu a s => s!"μ {ppCoVar a} . {ppStatementCtx vctx (a :: cctx) s}"

  def ppConsumerCtx (vctx : List Var) (cctx : List CoVar) : Consumer -> String
    | .covar a =>
        match a with
        | .bound i => ppCoVar (cctx.getD i (.free 0))
        | _ => ppCoVar a
    | .mu_tilde a s => s!"μ̃ {ppVar a} . {ppStatementCtx (a :: vctx) cctx s}"

  def ppStatementCtx (vctx : List Var) (cctx : List CoVar) : Statement -> String
    | .prim op p1 p2 c =>
        s!"{ppOp op}({ppProducerCtx vctx cctx p1}, {ppProducerCtx vctx cctx p2}; {ppConsumerCtx vctx cctx c})"
    | .ifz p s1 s2 =>
        s!"ifz({ppProducerCtx vctx cctx p}, {ppStatementCtx vctx cctx s1}, {ppStatementCtx vctx cctx s2})"
    | .cut p c => s!"⟨{ppProducerCtx vctx cctx p} | {ppConsumerCtx vctx cctx c}⟩"
end

def ppProducer (p : Producer) : String :=
  ppProducerCtx [] [] p

def ppConsumer (c : Consumer) : String :=
  ppConsumerCtx [] [] c

def ppStatement (s : Statement) : String :=
  ppStatementCtx [] [] s

instance : ToString Producer := ⟨ppProducer⟩
instance : ToString Consumer := ⟨ppConsumer⟩
instance : ToString Statement := ⟨ppStatement⟩

instance : ToFormat Producer := ⟨fun p => Std.Format.text (ppProducer p)⟩
instance : ToFormat Consumer := ⟨fun c => Std.Format.text (ppConsumer c)⟩
instance : ToFormat Statement := ⟨fun s => Std.Format.text (ppStatement s)⟩

end Core
