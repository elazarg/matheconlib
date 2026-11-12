/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import GameTheory.Math.ParametricOptimality
public import MathEconLib.RevealedPreference.BudgetRegularity
public import MathEconLib.RevealedPreference.Choice

/-!
# Closed native demand from a shared mathematical theorem

Prices, wealth and the utility objective may vary jointly. Demand retains every
feasible maximizer, including ties. The result concerns limits of maximizers;
it assumes neither existence of a maximizer nor compactness of budgets.
-/

@[expose] public section

namespace MathEconLibTest.RevealedPreference.ParametricDemandConsumer

open MathEconLib.RevealedPreference Set
open scoped NNReal

/-- The shared feasible-maximizer theorem applies to native commodity demand,
including zero wealth and parameter-dependent utility. -/
theorem isClosed_demandGraph {X : Type*} [TopologicalSpace X] {L : ℕ}
    (price : X → Bundle L) (priceContinuous : Continuous price)
    (positive : ∀ x i, 0 < price x i)
    (wealth : X → ℝ≥0) (wealthContinuous : Continuous wealth)
    (objective : X × Bundle L → ℝ) (objectiveContinuous : Continuous objective) :
    IsClosed {point : X × Bundle L |
      point.2 ∈ utilityChoice (fun bundle => objective (point.1, bundle))
        (linearBudgetSet (price point.1) (wealth point.1))} := by
  have canonical := GameTheory.Math.isClosed_feasibleMaximizers
    (fun x => linearBudgetSet (price x) (wealth x)) objective
    (linearBudgetSet_graph_closed price priceContinuous wealth wealthContinuous)
    (positivePriceBudget_lowerHemicontinuous price priceContinuous positive wealth wealthContinuous)
    objectiveContinuous
  have same : {point : X × Bundle L |
      point.2 ∈ utilityChoice (fun bundle => objective (point.1, bundle))
        (linearBudgetSet (price point.1) (wealth point.1))} =
      {point : X × Bundle L |
        point.2 ∈ linearBudgetSet (price point.1) (wealth point.1) ∧
          IsMaxOn (fun bundle => objective (point.1, bundle))
            (linearBudgetSet (price point.1) (wealth point.1)) point.2} := by
    ext point
    exact mem_utilityChoice _ _ _
  rw [same]
  exact canonical

end MathEconLibTest.RevealedPreference.ParametricDemandConsumer
