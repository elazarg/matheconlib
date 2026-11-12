/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.DemandRegularityControls

/-!
# Nonempty demand without a closed demand graph

The feasible budget graph is closed and utility is continuous, but a free-good
boundary destroys lower hemicontinuity. Every parameter still has an optimal
bundle: zero away from the boundary and quantity one at the boundary.
-/

@[expose] public section

namespace MathEconLibTest.RevealedPreference.DemandGraphBoundary

open MathEconLib.RevealedPreference Set Filter Topology
open MathEconLibTest.RevealedPreference.DemandRegularityControls

def peak (q : Bundle 1) : ℝ := -(q 0 - 1) ^ 2

theorem peak_continuous : Continuous peak :=
  (((continuous_apply (0 : Fin 1)).sub continuous_const).pow 2).neg

/-- A positive one-good price with zero wealth forces the entire bundle to zero. -/
theorem feasible_eq_zero {x : ℝ} (nonzero : x ≠ 0) {q : Bundle 1}
    (affordable : q ∈ freeBoundaryBudget x) : q = 0 := by
  have positivePrice : (0 : ℝ) < x ^ 2 := sq_pos_of_ne_zero nonzero
  have bound : x ^ 2 * q 0 ≤ 0 := by
    simpa [freeBoundaryBudget, linearBudgetSet, dot, dotProduct] using affordable.2
  have nonpositive : q 0 ≤ 0 :=
    nonpos_of_mul_nonpos_right bound positivePrice
  have quantityZero : q 0 = 0 := le_antisymm nonpositive (affordable.1 0)
  funext coordinate
  fin_cases coordinate
  exact quantityZero

theorem zero_feasible (x : ℝ) : (0 : Bundle 1) ∈ freeBoundaryBudget x := by
  refine ⟨fun _ => le_rfl, ?_⟩
  simp

theorem zero_chosen {x : ℝ} (nonzero : x ≠ 0) :
    (0 : Bundle 1) ∈ utilityChoice peak (freeBoundaryBudget x) := by
  apply (mem_utilityChoice peak _ _).mpr
  refine ⟨zero_feasible x, ?_⟩
  intro q affordable
  change peak q ≤ peak 0
  rw [feasible_eq_zero nonzero affordable]

private theorem one_feasible : (fun _ : Fin 1 => (1 : ℝ)) ∈ freeBoundaryBudget 0 := by
  constructor
  · intro coordinate
    norm_num
  · norm_num [freeBoundaryBudget, linearBudgetSet, dot, dotProduct]

theorem one_chosen :
    (fun _ : Fin 1 => (1 : ℝ)) ∈ utilityChoice peak (freeBoundaryBudget 0) := by
  apply (mem_utilityChoice peak _ _).mpr
  refine ⟨one_feasible, ?_⟩
  intro q _
  simpa [peak] using neg_nonpos.mpr (sq_nonneg (q 0 - 1))

theorem zero_not_chosen_at_zero :
    (0 : Bundle 1) ∉ utilityChoice peak (freeBoundaryBudget 0) := by
  intro chosen
  have impossible : peak (fun _ : Fin 1 => 1) ≤ peak 0 :=
    ((mem_utilityChoice peak _ _).mp chosen).2 one_feasible
  norm_num [peak] at impossible

theorem demand_nonempty (x : ℝ) : (utilityChoice peak (freeBoundaryBudget x)).Nonempty := by
  by_cases boundary : x = 0
  · subst x
    exact ⟨fun _ => 1, one_chosen⟩
  · exact ⟨0, zero_chosen boundary⟩

/-- Taking the continuous zero-bundle section exposes the failure of graph closedness. -/
theorem demand_graph_not_closed :
    ¬ IsClosed {point : ℝ × Bundle 1 |
      point.2 ∈ utilityChoice peak (freeBoundaryBudget point.1)} := by
  intro closed
  have zeroSectionClosed : IsClosed
      {x : ℝ | (0 : Bundle 1) ∈ utilityChoice peak (freeBoundaryBudget x)} :=
    closed.preimage (continuous_id.prodMk continuous_const)
  have nearby : {x : ℝ | (0 : Bundle 1) ∉ utilityChoice peak (freeBoundaryBudget x)} ∈
      𝓝 (0 : ℝ) := zeroSectionClosed.isOpen_compl.mem_nhds zero_not_chosen_at_zero
  obtain ⟨radius, positiveRadius, contained⟩ := Metric.mem_nhds_iff.mp nearby
  have inside : radius / 2 ∈ Metric.ball (0 : ℝ) radius := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos positiveRadius)]
    linarith
  exact (contained inside) (zero_chosen (ne_of_gt (half_pos positiveRadius)))

/-- Closed feasibility, a continuous objective, and attained demand do not replace recovery. -/
theorem closed_feasibility_nonempty_demand_not_closed :
    Continuous peak ∧
      IsClosed {point : ℝ × Bundle 1 | point.2 ∈ freeBoundaryBudget point.1} ∧
      (∀ x, (utilityChoice peak (freeBoundaryBudget x)).Nonempty) ∧
      ¬ IsClosed {point : ℝ × Bundle 1 |
        point.2 ∈ utilityChoice peak (freeBoundaryBudget point.1)} :=
  ⟨peak_continuous, freeBoundary_graph_closed, demand_nonempty, demand_graph_not_closed⟩

end MathEconLibTest.RevealedPreference.DemandGraphBoundary
