import Lamumu.Basic
import Lamumu.Notation

namespace Core

open Std

def ppVar (v : Var) : String :=
  s!"x_{v}"

def ppCoVar : CoVar → String
  | .star => "★"
  | .idx n => s!"α_{n}"

def ppOp : Op -> String
  | .add => "+"
  | .mul => "*"
  | .sub => "-"

mutual
  def ppProducer : Producer -> String
    | .var v => ppVar v
    | .lit n => s!"⌜{n}⌝"
    | .mu a s => s!"μ {ppCoVar a} . {ppStatement s}"

  def ppConsumer : Consumer -> String
    | .covar a => ppCoVar a
    | .mu_tilde a s => s!"μ̃ {ppVar a} . {ppStatement s}"

  def ppStatement : Statement -> String
    | .prim op p1 p2 c => s!"{ppOp op}({ppProducer p1}, {ppProducer p2}; {ppConsumer c})"
    | .ifz p s1 s2 => s!"ifz({ppProducer p}, {ppStatement s1}, {ppStatement s2})"
    | .cut p c => s!"⟨{ppProducer p} | {ppConsumer c}⟩"
end

instance : ToString Producer := ⟨ppProducer⟩
instance : ToString Consumer := ⟨ppConsumer⟩
instance : ToString Statement := ⟨ppStatement⟩

instance : ToFormat Producer := ⟨fun p => Std.Format.text (ppProducer p)⟩
instance : ToFormat Consumer := ⟨fun c => Std.Format.text (ppConsumer c)⟩
instance : ToFormat Statement := ⟨fun s => Std.Format.text (ppStatement s)⟩

end Core
