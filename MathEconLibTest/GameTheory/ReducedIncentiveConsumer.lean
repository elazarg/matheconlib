/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.SupportingSlopes.Convexity
public import MathEconLib.SingleParameter.Payment
public import Mathlib.Tactic.NormNum

/-!
# Reduced incentive inequalities beyond bounded allocations

Supporting slopes describe utility and quantity directly, including quantities
outside the unit interval. A bounded native choice problem can reuse its payment
identity through the same inequality. That inequality compares assigned reports;
an unused subsidized action can still defeat universal incentive compatibility.
-/

@[expose] public section

namespace MathEconLibTest.AbstractionExperiments.ReducedIncentiveConsumer

open Set MathEconLib

noncomputable section

def multiQuantity (v : ℝ) : ℝ := 2 * v

def multiUtility (v : ℝ) : ℝ := v ^ 2

theorem multi_support : SupportingSlopesOn multiUtility multiQuantity univ := by
  intro x _ y _
  dsimp [multiQuantity, multiUtility]
  nlinarith [sq_nonneg (x - y)]

theorem multi_monotone : MonotoneOn multiQuantity univ :=
  multi_support.monotoneOn

theorem multi_convex : ConvexOn ℝ univ multiUtility :=
  multi_support.convexOn convex_univ

/-- Charging the square of a report implements these unbounded quantities truthfully. -/
theorem multi_reportIC (trueType report : ℝ) :
    trueType * multiQuantity report - report ^ 2 ≤ multiUtility trueType := by
  have bound := multi_support.report_payoff_le (mem_univ trueType) (mem_univ report)
  dsimp [multiQuantity, multiUtility] at bound ⊢
  nlinarith

theorem multi_nonnegative {v : ℝ} (hv : 0 ≤ v) : 0 ≤ multiQuantity v :=
  mul_nonneg (by norm_num) hv

/-- Nonnegative types already generate quantities with no finite upper bound. -/
theorem multi_unbounded (bound : ℝ) : ∃ v ∈ Ici (0 : ℝ), bound < multiQuantity v := by
  refine ⟨max 0 (bound + 1), le_max_left _ _, ?_⟩
  dsimp [multiQuantity]
  linarith [le_max_left (0 : ℝ) (bound + 1), le_max_right (0 : ℝ) (bound + 1)]

theorem multi_quantity_two_exceeds_unit : 1 < multiQuantity 2 := by
  norm_num [multiQuantity]

/-- The native unit-allocation structure cannot represent this quantity rule. -/
theorem native_quantity_ne_multi {Action : Type*} (P : SingleParameterProblem Action) :
    P.q ≠ multiQuantity := by
  intro equal
  have bounded := (P.q_range 2).2
  rw [equal] at bounded
  norm_num [multiQuantity] at bounded

/-- The prescribed action leaves an unused action that pays the agent one unit. -/
def unusedSubsidy : SingleParameterProblem Bool where
  lowestType := 0
  highestType := 1
  allocation _ := 0
  allocation_range _ := by constructor <;> norm_num
  payment action := if action then -1 else 0
  strategy _ := false

theorem unused_support :
    SupportingSlopesOn unusedSubsidy.U unusedSubsidy.q unusedSubsidy.typeInterval := by
  intro x _ y _
  simp [SingleParameterProblem.U, SingleParameterProblem.payoff,
    SingleParameterProblem.q, unusedSubsidy]

theorem unused_envelopeIC : SingleParameterProblem.HasEnvelopeIC unusedSubsidy :=
  ⟨unused_support⟩

theorem unused_reportIC : SingleParameterProblem.HasTypeDeviationIC unusedSubsidy := by
  constructor
  intro x _ y _
  simp [SingleParameterProblem.payoff, unusedSubsidy]

/-- Every report in the reduced problem induces the same unsubsidized action. -/
theorem unused_reduced_universalIC :
    SingleParameterProblem.HasUniversalIC unusedSubsidy.reduce univ := by
  constructor
  · intro _ _
    exact mem_univ _
  · intro x _ report _
    simp [SingleParameterProblem.reduce, SingleParameterProblem.payoff,
      SingleParameterProblem.q, unusedSubsidy]

/-- Type zero gains strictly by using the omitted action. -/
theorem unused_not_universalIC :
    ¬ SingleParameterProblem.HasUniversalIC unusedSubsidy univ := by
  intro universal
  have profitable := universal.universalIC 0
    (by norm_num [SingleParameterProblem.typeInterval, unusedSubsidy]) true (mem_univ _)
  norm_num [SingleParameterProblem.payoff, unusedSubsidy] at profitable

/-- A direct supporting-slope hypothesis feeds the existing native payment theorem. -/
theorem payment_identity_of_supportingSlopes {Action : Type*}
    (P : SingleParameterProblem Action)
    (support : SupportingSlopesOn P.U P.q P.typeInterval)
    (v : ℝ) (hv : v ∈ P.typeInterval) :
    P.payment (P.strategy v) =
      v * P.q v - P.U P.lowestType - ∫ w in P.lowestType..v, P.q w := by
  let _ : SingleParameterProblem.HasEnvelopeIC P := ⟨support⟩
  exact P.payment_identity v hv

end

end MathEconLibTest.AbstractionExperiments.ReducedIncentiveConsumer
