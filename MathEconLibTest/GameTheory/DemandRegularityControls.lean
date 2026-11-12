/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.RevealedPreference.BudgetRegularity
public import MathEconLib.RevealedPreference.Choice
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Budget recovery and retained demand ties

A continuously vanishing price with zero wealth has a closed feasible graph
but fails lower hemicontinuity. Separately, linear utility on a two-good budget
retains two distinct optimal bundles rather than imposing a selected demand.
-/

@[expose] public section

namespace MathEconLibTest.RevealedPreference.DemandRegularityControls

open MathEconLib.RevealedPreference Set Filter Topology
open scoped NNReal

/-- At the zero price every nonnegative quantity is free; elsewhere only zero is affordable. -/
def freeBoundaryBudget (x : ℝ) : Set (Bundle 1) :=
  linearBudgetSet (fun _ => x ^ 2) 0

theorem freeBoundary_graph_closed :
    IsClosed {point : ℝ × Bundle 1 | point.2 ∈ freeBoundaryBudget point.1} :=
  linearBudgetSet_graph_closed (fun x : ℝ => fun _ : Fin 1 => x ^ 2)
    (continuous_pi fun _ => continuous_id.pow 2) (fun _ => (0 : ℝ≥0)) continuous_const

/-- Closed feasibility alone cannot supply nearby access to a free positive quantity. -/
theorem freeBoundary_not_lowerHemicontinuousAt :
    ¬ LowerHemicontinuousAt freeBoundaryBudget 0 := by
  intro lower
  let quantities : Set (Bundle 1) := {q | (1 / 2 : ℝ) < q 0}
  have openQuantities : IsOpen quantities :=
    isOpen_lt continuous_const (continuous_apply (0 : Fin 1))
  have hit : (freeBoundaryBudget 0 ∩ quantities).Nonempty := by
    refine ⟨fun _ => 1, ?_, ?_⟩
    · constructor
      · intro i
        norm_num
      · norm_num [freeBoundaryBudget, linearBudgetSet, dot, dotProduct]
    · norm_num [quantities]
  have nearby : {x | (freeBoundaryBudget x ∩ quantities).Nonempty} ∈ 𝓝 (0 : ℝ) :=
    (lowerHemicontinuousAt_iff.mp lower) quantities openQuantities hit
  obtain ⟨radius, positiveRadius, contained⟩ := Metric.mem_nhds_iff.mp nearby
  have inside : radius / 2 ∈ Metric.ball (0 : ℝ) radius := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos positiveRadius)]
    linarith
  obtain ⟨q, affordable, large⟩ := contained inside
  have bound : (radius / 2) ^ 2 * q 0 ≤ 0 := by
    simpa [freeBoundaryBudget, linearBudgetSet, dot, dotProduct] using affordable.2
  have positiveSquare : (0 : ℝ) < (radius / 2) ^ 2 :=
    sq_pos_of_pos (half_pos positiveRadius)
  have positiveQuantity : 0 < q 0 := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) large
  exact (not_lt_of_ge bound) (mul_pos positiveSquare positiveQuantity)

def unitPrice : Bundle 2 := fun _ => 1

def firstCorner : Bundle 2 := fun good => if good = 0 then 1 else 0

def secondCorner : Bundle 2 := fun good => if good = 0 then 0 else 1

def linearUtility (q : Bundle 2) : ℝ := dot unitPrice q

theorem linearUtility_continuous : Continuous linearUtility := continuous_dot unitPrice

theorem corners_distinct : firstCorner ≠ secondCorner := by
  intro equal
  have impossible := congrFun equal 0
  norm_num [firstCorner, secondCorner] at impossible

/-- Both corners remain members of the same native maximizing correspondence. -/
theorem both_corners_chosen :
    firstCorner ∈ utilityChoice linearUtility (linearBudgetSet unitPrice 1) ∧
      secondCorner ∈ utilityChoice linearUtility (linearBudgetSet unitPrice 1) := by
  have select (q : Bundle 2) (nonnegative : Nonnegative q) (spent : dot unitPrice q = 1) :
      q ∈ utilityChoice linearUtility (linearBudgetSet unitPrice 1) := by
    apply (mem_utilityChoice linearUtility _ q).mpr
    refine ⟨⟨nonnegative, spent.le⟩, ?_⟩
    intro alternative offered
    change dot unitPrice alternative ≤ dot unitPrice q
    rw [spent]
    exact offered.2
  constructor
  · apply select
    · intro good
      fin_cases good <;> norm_num [firstCorner]
    · norm_num [unitPrice, firstCorner, dot, dotProduct]
  · apply select
    · intro good
      fin_cases good <;> norm_num [secondCorner]
    · norm_num [unitPrice, secondCorner, dot, dotProduct]

end MathEconLibTest.RevealedPreference.DemandRegularityControls
