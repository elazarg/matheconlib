/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.SupportingSlopes
public import MathEconLib.ForMathlib.SupportingForms.Convexity

/-!
# Convexity from affine lower supports

Supporting slopes imply convexity on a convex domain, without a slope bound
or a regularity assumption on either function.
-/

@[expose] public section

namespace MathEconLib.SupportingSlopesOn

/-- Affine lower supports at all points imply convexity on a convex domain. -/
theorem convexOn {U q : ℝ → ℝ} {S : Set ℝ} (h : SupportingSlopesOn U q S)
    (hS : Convex ℝ S) : ConvexOn ℝ S U :=
  SupportingFormsOn.convexOn (q := fun y => LinearMap.mulRight ℝ (q y)) h hS

end MathEconLib.SupportingSlopesOn
