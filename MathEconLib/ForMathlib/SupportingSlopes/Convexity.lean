/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.SupportingSlopes
public import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convexity from affine lower supports

Supporting slopes imply convexity on a convex domain, without a slope bound
or a regularity assumption on either function.
-/

@[expose] public section

namespace MathEconLib.SupportingSlopesOn

/-- Affine lower supports at all points imply convexity on a convex domain. -/
theorem convexOn {U q : ℝ → ℝ} {S : Set ℝ} (h : SupportingSlopesOn U q S)
    (hS : Convex ℝ S) : ConvexOn ℝ S U := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a * x + b * y
  have hz : z ∈ S := hS hx hy ha hb hab
  have lowerX := mul_le_mul_of_nonneg_left (h x hx z hz) ha
  have lowerY := mul_le_mul_of_nonneg_left (h y hy z hz) hb
  have cancel : a * ((x - z) * q z) + b * ((y - z) * q z) = 0 := by
    calc
      _ = (a * x + b * y - (a + b) * z) * q z := by ring
      _ = 0 := by rw [hab]; dsimp [z]; ring
  have weighted : a * (U x - U z) + b * (U y - U z) =
      a * U x + b * U y - U z := by
    calc
      _ = a * U x + b * U y - (a + b) * U z := by ring
      _ = _ := by rw [hab, one_mul]
  change U z ≤ a * U x + b * U y
  linarith

end MathEconLib.SupportingSlopesOn
