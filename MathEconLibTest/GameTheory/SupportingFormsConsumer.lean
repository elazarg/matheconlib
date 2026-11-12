/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.SupportingForms.Convexity
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Quadratic report incentives and the obstruction from rotation

Linear-form supports implement truthful reports with quadratic payments in two
dimensions. Pairwise monotonicity alone cannot produce such a potential: a
rotation field has zero pairwise pairing but a strictly positive triangular cycle.
-/

@[expose] public section

namespace MathEconLibTest.AbstractionExperiments.SupportingFormsConsumer

open Set MathEconLib
open scoped BigOperators

noncomputable section

abbrev Plane := ℝ × ℝ

def quantity (v : Plane) : Plane →ₗ[ℝ] ℝ :=
  (2 * v.1) • LinearMap.fst ℝ ℝ ℝ + (2 * v.2) • LinearMap.snd ℝ ℝ ℝ

@[simp] theorem quantity_apply (v x : Plane) :
    quantity v x = 2 * v.1 * x.1 + 2 * v.2 * x.2 := rfl

def quadraticUtility (v : Plane) : ℝ := v.1 ^ 2 + v.2 ^ 2

theorem quadratic_support : SupportingFormsOn quadraticUtility quantity univ := by
  intro x _ y _
  simp only [quantity_apply, quadraticUtility, Prod.fst_sub, Prod.snd_sub]
  nlinarith [sq_nonneg (x.1 - y.1), sq_nonneg (x.2 - y.2)]

theorem quadratic_convex : ConvexOn ℝ univ quadraticUtility :=
  quadratic_support.convexOn convex_univ

/-- Truth maximizes utility when payment is the sum of squared report coordinates. -/
theorem quadratic_reportIC (trueType report : Plane) :
    quantity report trueType - quadraticUtility report ≤ quadraticUtility trueType := by
  have bound := quadratic_support.report_payoff_le (mem_univ trueType) (mem_univ report)
  simp only [quantity_apply, quadraticUtility] at bound ⊢
  nlinarith

def rotation (v : Plane) : Plane →ₗ[ℝ] ℝ :=
  (-v.2) • LinearMap.fst ℝ ℝ ℝ + v.1 • LinearMap.snd ℝ ℝ ℝ

@[simp] theorem rotation_apply (v x : Plane) :
    rotation v x = -v.2 * x.1 + v.1 * x.2 := rfl

/-- The rotation field passes every pairwise monotonicity comparison with equality. -/
theorem rotation_pairing_zero (x y : Plane) : (rotation x - rotation y) (x - y) = 0 := by
  simp only [LinearMap.sub_apply, rotation_apply, Prod.fst_sub, Prod.snd_sub]
  ring

theorem rotation_pairwise_monotone (x y : Plane) :
    0 ≤ (rotation x - rotation y) (x - y) := by
  rw [rotation_pairing_zero]

def triangle : Fin 3 → Plane
  | 0 => (0, 0)
  | 1 => (1, 0)
  | _ => (0, 1)

def triangleNext : Fin 3 ≃ Fin 3 :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

/-- The directed cycle is `0 → e₁ → e₂ → 0`, with the support sign convention. -/
theorem rotation_cycle_gain :
    (∑ i : Fin 3, rotation (triangle i) (triangle (triangleNext i) - triangle i)) = 1 := by
  norm_num [Fin.sum_univ_succ, triangleNext, Equiv.swap_apply_def, triangle, rotation]

/-- Summing the hypothetical support inequalities contradicts the concrete cycle. -/
theorem rotation_no_supporting_potential :
    ¬ ∃ utility : Plane → ℝ, SupportingFormsOn utility rotation univ := by
  rintro ⟨utility, support⟩
  have bound := support.sum_cycle_le_zero triangle (fun _ => mem_univ _) triangleNext
  rw [rotation_cycle_gain] at bound
  norm_num at bound

end

end MathEconLibTest.AbstractionExperiments.SupportingFormsConsumer
