/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.RevealedPreference.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Regularity of nonnegative linear budgets

Strictly positive prices permit continuous recovery of feasible bundles even
at zero wealth. Closedness of the feasible graph requires only continuity.
-/

@[expose] public section

namespace MathEconLib.RevealedPreference

open MathEconLib.RevealedPreference Set Filter Topology
open scoped NNReal

/-- Strictly positive commodity prices allow continuous recovery of every
feasible nonnegative bundle, even when wealth is zero. No demand selection,
compactness, or finite observation set is assumed. -/
theorem positivePriceBudget_lowerHemicontinuous
    {X : Type*} [TopologicalSpace X] {L : ℕ}
    (price : X → Bundle L) (continuous_price : Continuous price)
    (positive_price : ∀ x i, 0 < price x i)
    (wealth : X → ℝ≥0) (continuous_wealth : Continuous wealth) :
    LowerHemicontinuous (fun x => linearBudgetSet (price x) (wealth x)) := by
  intro reference
  apply lowerHemicontinuousAt_iff.mpr
  rintro openSet isOpenSet ⟨bundle, feasible, offered⟩
  by_cases zero : bundle = 0
  · subst bundle
    exact Eventually.of_forall fun next =>
      ⟨0, ⟨fun _ => le_rfl, by simp⟩, offered⟩
  · let cost (x : X) : ℝ := dot (price x) bundle
    have cost_positive (x : X) : 0 < cost x := by
      have dominance : StrictDominates bundle 0 := ⟨feasible.1, zero⟩
      simpa only [dot_zero_right] using
        dot_strictlyIncreasing_of_pos (positive_price x) dominance
    let factor (x : X) : ℝ := min 1 ((wealth x : ℝ) / cost x)
    have cost_continuous : Continuous cost :=
      continuous_price.dotProduct continuous_const
    have wealth_real_continuous : Continuous (fun x => (wealth x : ℝ)) :=
      NNReal.continuous_coe.comp continuous_wealth
    have factor_continuous : Continuous factor :=
      continuous_const.min
        (wealth_real_continuous.div cost_continuous (fun x => (cost_positive x).ne'))
    have factor_nonnegative (x : X) : 0 ≤ factor x :=
      le_min zero_le_one (div_nonneg (wealth x).property (cost_positive x).le)
    have recovery_continuous : Continuous (fun x => factor x • bundle) :=
      factor_continuous.smul continuous_const
    have recovery_reference : factor reference • bundle = bundle := by
      have ratio_at_least_one : 1 ≤ (wealth reference : ℝ) / cost reference :=
        (le_div_iff₀ (cost_positive reference)).mpr (by simpa only [one_mul] using feasible.2)
      change min 1 ((wealth reference : ℝ) / cost reference) • bundle = bundle
      rw [min_eq_left ratio_at_least_one, one_smul]
    have recovery_nonnegative (x : X) : Nonnegative (factor x • bundle) := by
      intro coordinate
      change 0 ≤ factor x * bundle coordinate
      exact mul_nonneg (factor_nonnegative x) (feasible.1 coordinate)
    have recovery_affordable (x : X) : dot (price x) (factor x • bundle) ≤ (wealth x : ℝ) := by
      calc
        dot (price x) (factor x • bundle) = factor x * cost x := by
          simp only [dot, dotProduct_smul, smul_eq_mul, cost]
        _ ≤ ((wealth x : ℝ) / cost x) * cost x :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (cost_positive x).le
        _ = (wealth x : ℝ) := div_mul_cancel₀ _ (cost_positive x).ne'
    have recovery_offered : factor reference • bundle ∈ openSet := by
      rw [recovery_reference]
      exact offered
    filter_upwards [(recovery_continuous.tendsto reference).eventually
      (isOpenSet.mem_nhds recovery_offered)] with next recovered
    exact ⟨factor next • bundle,
      ⟨recovery_nonnegative next, recovery_affordable next⟩, recovered⟩

/-- Budget feasibility is closed under jointly converging prices, wealth and
bundles. This result needs continuity, but no strict-price assumption. -/
theorem linearBudgetSet_graph_closed
    {X : Type*} [TopologicalSpace X] {L : ℕ}
    (price : X → Bundle L) (continuous_price : Continuous price)
    (wealth : X → ℝ≥0) (continuous_wealth : Continuous wealth) :
    IsClosed {point : X × Bundle L |
      point.2 ∈ linearBudgetSet (price point.1) (wealth point.1)} := by
  have nonnegative_closed : IsClosed {point : X × Bundle L | Nonnegative point.2} := by
    have same : {point : X × Bundle L | Nonnegative point.2} =
        ⋂ coordinate : Fin L, {point : X × Bundle L | 0 ≤ point.2 coordinate} := by
      ext point
      simp only [Nonnegative, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [same]
    exact isClosed_iInter fun coordinate =>
      isClosed_le continuous_const ((continuous_apply coordinate).comp continuous_snd)
  have joint_cost_continuous : Continuous (fun point : X × Bundle L =>
      dot (price point.1) point.2) :=
    (continuous_price.comp continuous_fst).dotProduct continuous_snd
  have joint_wealth_continuous : Continuous (fun point : X × Bundle L =>
      (wealth point.1 : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_wealth.comp continuous_fst)
  exact nonnegative_closed.inter (isClosed_le joint_cost_continuous joint_wealth_continuous)

end MathEconLib.RevealedPreference
