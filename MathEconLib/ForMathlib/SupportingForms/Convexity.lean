/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.SupportingForms
public import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convexity from supporting linear forms

Affine lower supports at every point imply convexity on a convex domain.
No continuity, finite dimension or inner product is required.
-/

@[expose] public section

namespace MathEconLib.SupportingFormsOn

/-- Supporting linear forms imply convexity on every convex supporting domain. -/
theorem convexOn {E : Type*} [AddCommGroup E] [Module ℝ E]
    {U : E → ℝ} {q : E → E →ₗ[ℝ] ℝ} {S : Set E}
    (h : SupportingFormsOn U q S) (hS : Convex ℝ S) : ConvexOn ℝ S U := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ S := hS hx hy ha hb hab
  have lowerX := mul_le_mul_of_nonneg_left (h x hx z hz) ha
  have lowerY := mul_le_mul_of_nonneg_left (h y hy z hz) hb
  have rearrange : a • (x - z) + b • (y - z) = a • x + b • y - (a + b) • z := by
    rw [smul_sub, smul_sub, add_smul]
    abel
  have cancel : a * q z (x - z) + b * q z (y - z) = 0 := by
    calc
      _ = q z (a • (x - z) + b • (y - z)) := by
        simp only [map_add, map_smul, smul_eq_mul]
      _ = q z (a • x + b • y - (a + b) • z) := congrArg (q z) rearrange
      _ = 0 := by
        rw [hab, one_smul]
        simp only [z, sub_self, map_zero]
  have weighted : a * (U x - U z) + b * (U y - U z) = a * U x + b * U y - U z := by
    calc
      _ = a * U x + b * U y - (a + b) * U z := by ring
      _ = _ := by rw [hab, one_mul]
  change U z ≤ a * U x + b * U y
  linarith

end MathEconLib.SupportingFormsOn
