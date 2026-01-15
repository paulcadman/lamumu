import Lamumu

open Evaluate
open Core

def showEval : Except EvalError Statement → String
  | .ok s => toString s
  | .error ⟨s⟩ => s!"Eval stuck at: {s}"

-- Example 2.2. FUN: let x = ⌜2⌝ * ⌜2⌝ in x * x
#eval ⟨μ α_0 . ⟨μ α_1 . ⟨μ α_2 . *(⌜2⌝, ⌜2⌝; α_2) | μ̃ x_0 . ⟨μ α_3 . *(x_0, x_0; α_3) | α_1⟩⟩ | α_0⟩ | ★⟩
  |> step --      ⟨μ α_2 . ⟨μ α_4 . *(⌜2⌝, ⌜2⌝; α_4) | μ̃ x_2 . ⟨μ α_7 . *(x_2, x_2; α_7) | α_2⟩⟩ | ★⟩
  |>.bind step -- ⟨μ α_5 . *(⌜2⌝, ⌜2⌝; α_5) | μ̃ x_3 . ⟨μ α_9 . *(x_3, x_3; α_9) | ★⟩⟩
  |>.bind step -- *(⌜2⌝, ⌜2⌝; μ̃ x_3 . ⟨μ α_9 . *(x_3, x_3; α_9) | ★⟩)
  |>.bind step -- ⟨⌜4⌝ | μ̃ x_3 . ⟨μ α_9 . *(x_3, x_3; α_9) | ★⟩⟩
  |>.bind step -- ⟨μ α_10 . *(⌜4⌝, ⌜4⌝; α_10) | ★⟩
  |>.bind step -- *(⌜4⌝, ⌜4⌝; ★)
  |>.bind step -- ⟨⌜16⌝ | ★⟩
  |> showEval

-- Example that needs focusing
#eval ⟨μ α_0 . (*(⌜4⌝, (μ α_1 . *(⌜2⌝, ⌜3⌝; α_1)); α_0)) | ★⟩
  |> step -- *(⌜4⌝, μ α_2 . *(⌜2⌝, ⌜3⌝; α_2); ★)
  |>.map Focus.focusStatement -- ⟨μ α_2 . *(⌜2⌝, ⌜3⌝; α_2) | μ̃ x_0 . *(⌜4⌝, x_0; ★)⟩
  |>.bind step -- *(⌜2⌝, ⌜3⌝; μ̃ x_0 . *(⌜4⌝, x_0; ★))
  |>.bind step -- ⟨⌜6⌝ | μ̃ x_0 . *(⌜4⌝, x_0; ★)⟩
  |>.bind step -- *(⌜4⌝, ⌜6⌝; ★)
  |>.bind step -- ⟨⌜24⌝ | ★⟩
  |> showEval

def main : IO Unit :=
  IO.println "hello"
