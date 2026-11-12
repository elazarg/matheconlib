/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.PotentialBounds
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Supporting linear forms on a set

A selected linear form gives an affine lower support to the utility at each
point. No topology, inner product or dimensionality assumption is imposed.
Supporting forms give monotone pairings and nonpositive finite cycle sums.
-/

@[expose] public section

namespace MathEconLib

universe u

/-- At every point of the set, its selected affine form supports the utility from below. -/
abbrev SupportingFormsOn {E : Type u} [AddCommGroup E] [Module ℝ E]
    (U : E → ℝ) (q : E → E →ₗ[ℝ] ℝ) (S : Set E) : Prop :=
  PotentialBoundsOn U (fun y x => q y (x - y)) S

namespace SupportingFormsOn

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
  {U : E → ℝ} {q : E → E →ₗ[ℝ] ℝ} {S : Set E}

/-- The canonical payment makes each offered report no better than the assigned utility. -/
theorem report_payoff_le (h : SupportingFormsOn U q S)
    {trueType report : E} (trueMember : trueType ∈ S) (reportMember : report ∈ S) :
    q report trueType - (q report report - U report) ≤ U trueType := by
  have support := h trueType trueMember report reportMember
  dsimp only at support
  rw [map_sub] at support
  linarith

/-- Supporting forms are monotone in the pairing with the difference of their base points. -/
theorem monotone_pairing (h : SupportingFormsOn U q S) {x y : E}
    (hx : x ∈ S) (hy : y ∈ S) : 0 ≤ (q x - q y) (x - y) := by
  have lower := h x hx y hy
  have upper := h y hy x hx
  dsimp only at lower upper
  rw [← neg_sub x y, map_neg] at upper
  change 0 ≤ q x (x - y) - q y (x - y)
  linarith

open scoped BigOperators

/-- Summing support inequalities along any finite permutation cancels the utility differences. -/
theorem sum_cycle_le_zero (h : SupportingFormsOn U q S) {ι : Type*} [Fintype ι]
    (points : ι → E) (members : ∀ i, points i ∈ S) (next : ι ≃ ι) :
    (∑ i, q (points i) (points (next i) - points i)) ≤ 0 :=
  PotentialBoundsOn.sum_cycle_le_zero h points members next

end SupportingFormsOn

end MathEconLib
