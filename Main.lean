import Lamumu

open Evaluate
open Focus

namespace CoreExamples

open Core
open scoped Core

def traceEval (e : Except EvalError Statement) : Except EvalError Statement :=
  match e with
  | .ok s => dbgTrace s!"Eval: {s}" (fun _ => e)
  | .error ⟨s⟩ => dbgTrace s!"Eval stuck at: {s}" (fun _ => e)

-- Example 2.2. FUN: let x = ⌜2⌝ * ⌜2⌝ in x * x
def ex1 := ⟨μ α_0 . ⟨μ α_1 . ⟨μ α_2 . *(⌜2⌝, ⌜2⌝; α_2) | μ̃ x_0 . ⟨μ α_3 . *(x_0, x_0; α_3) | α_1⟩⟩ | α_0⟩ | ★⟩
  |> step --      ⟨μ α_1 . ⟨μ α_2 . *(⌜2⌝, ⌜2⌝; α_2) | μ̃ x_0 . ⟨μ α_3 . *(x_0, x_0; α_3) | α_1⟩⟩ | ★⟩
  |>.bind step -- ⟨μ α_2 . *(⌜2⌝, ⌜2⌝; α_2) | μ̃ x_0 . ⟨μ α_3 . *(x_0, x_0; α_3) | ★⟩⟩
  |>.bind step -- *(⌜2⌝, ⌜2⌝; μ̃ x_0 . ⟨μ α_3 . *(x_0, x_0; α_3) | ★⟩)
  |>.bind step -- ⟨⌜4⌝ | μ̃ x_0 . ⟨μ α_3 . *(x_0, x_0; α_3) | ★⟩⟩
  |>.bind step -- ⟨μ α_3 . *(⌜4⌝, ⌜4⌝; α_3) | ★⟩
  |>.bind step -- *(⌜4⌝, ⌜4⌝; ★)
  |>.bind step -- ⟨⌜16⌝ | ★⟩

#guard ex1 = .ok ⟨⌜16⌝ | ★⟩

-- Example that needs focusing
def ex2 := ⟨μ α_0 . (*(⌜4⌝, (μ α_1 . *(⌜2⌝, ⌜3⌝; α_1)); α_0)) | ★⟩
  |> step --      *(⌜4⌝, μ α_1 . *(⌜2⌝, ⌜3⌝; α_1); ★)
  |>.map focus -- ⟨μ α_1 . *(⌜2⌝, ⌜3⌝; α_1) | μ̃ x_0 . *(⌜4⌝, x_0; ★)⟩
  |>.bind step -- *(⌜2⌝, ⌜3⌝; μ̃ x_0 . *(⌜4⌝, x_0; ★))
  |>.bind step -- ⟨⌜6⌝ | μ̃ x_0 . *(⌜4⌝, x_0; ★)⟩
  |>.bind step -- *(⌜4⌝, ⌜6⌝; ★)
  |>.bind step -- ⟨⌜24⌝ | ★⟩

#guard ex2 = .ok ⟨⌜24⌝ | ★⟩

end CoreExamples

namespace FunExamples

open Fun

open scoped Fun

-- Translate a term from Fun to Core
def fun_ex1 : Except EvalError Core.Statement :=
  (⌜2⌝ * ⌜3⌝)
  |> Fun.translate
  |> step
  |>.bind step

open scoped Core in
#guard fun_ex1 = .ok ⟨⌜6⌝ | ★⟩

def fun_ex_let : Except EvalError Core.Statement :=
  (let x_0 := ⌜2⌝ in x_0 + ⌜3⌝)
  |> Fun.translate
  |> step
  |>.bind step
  |>.bind step
  |>.bind step

open scoped Core in
#guard fun_ex_let = .ok ⟨⌜5⌝ | ★⟩

end FunExamples

def main : IO Unit :=
  IO.println "hello"
