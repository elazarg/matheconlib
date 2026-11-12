/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.UniformBoundaryEquilibrium
public import MathEconLibExamples.AllPurchase.UniformPriceFamilyProfit

/-!
# Boundary profit versus the uniform interior price family

The actual boundary equilibrium at price `5/2` sells one unit on average and
has bundled profit `3/2` at production cost one. Every supplied interior
family equilibrium earns strictly less at that cost, with square gap
`2/3 * (p - 5/2)^2`. The boundary strategy is certified separately; it is not
assigned a strict interior-regime certificate. No other prices or regimes
are asserted to exist or to be dominated.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase

open MeasureTheory ProbabilityTheory Set
open UniformProbability

namespace UniformBoundaryEquilibrium

/-- The actual equilibrium's aggregate purchases equal one. -/
theorem expectedAggregateBid_eq : model.expectedAggregateBid strategy = 1 := by
  rw [model.toAuction.expectedAggregateBid_eq_mul_mean strategy strategy_measurable
    strategy_integrable, mean_strategy]
  norm_num

/-- Actual receipts less production cost at the supplied boundary equilibrium. -/
theorem bundledProfit_eq : model.bundledProfit model.spec strategy 1 = 3 / 2 := by
  change ((5 / 2 : ℝ) - 1) * model.expectedAggregateBid strategy = _
  rw [expectedAggregateBid_eq]
  norm_num

private theorem bundledProfit_eq_scalar_optimum :
    model.bundledProfit model.spec strategy 1 =
      MathEconLib.AllPurchase.sellerProfitInterior 3 1 1 (1 / 2) 2
        (MathEconLib.AllPurchase.optimalPriceInterior 3 1 1 (1 / 2)) := by
  rw [bundledProfit_eq]
  norm_num [MathEconLib.AllPurchase.sellerProfitInterior,
    MathEconLib.AllPurchase.interiorMeanQuantity, MathEconLib.AllPurchase.optimalPriceInterior]

/-- The scalar square identity compares actual profits across the two certified regimes. -/
theorem interior_profit_gap (price : UniformPriceFamily.Price) :
    model.bundledProfit model.spec strategy 1 -
        (UniformPriceFamily.model price).bundledProfit (UniformPriceFamily.model price).spec
          (UniformPriceFamily.strategy price) 1 =
      (2 / 3 : ℝ) * (price.val - 5 / 2) ^ 2 := by
  have comparator := (UniformPriceFamily.model price).bundledProfit_eq_sellerProfitInterior
    (UniformPriceFamily.strategy price) (UniformPriceFamily.interior_strategy price) 1
  rw [UniformPriceFamily.expectedSqrtAllPayBid_eq] at comparator
  change _ = MathEconLib.AllPurchase.sellerProfitInterior 3 1 1 (1 / 2) 2 price.val at comparator
  rw [bundledProfit_eq_scalar_optimum, comparator]
  have gap := MathEconLib.AllPurchase.sellerProfitInterior_optimal_sub
    (φbar := 3) (α := 1) (c := 1) (M := 1 / 2) (n := 2)
    (by norm_num) (by norm_num) price.val
  norm_num [MathEconLib.AllPurchase.optimalPriceInterior] at gap ⊢
  exact gap

/-- Every actual strictly interior family member earns less than the boundary equilibrium. -/
theorem interior_profit_lt_boundary (price : UniformPriceFamily.Price) :
    (UniformPriceFamily.model price).bundledProfit (UniformPriceFamily.model price).spec
        (UniformPriceFamily.strategy price) 1 < model.bundledProfit model.spec strategy 1 := by
  have gap := interior_profit_gap price
  have nonzero : price.val - 5 / 2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt price.property.2)
  have positive : 0 < (2 / 3 : ℝ) * (price.val - 5 / 2) ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_ne_zero nonzero)
  linarith

/-- The comparison is between the two actual auction profit operations at the same cost. -/
theorem interior_profit_le_boundary (price : UniformPriceFamily.Price) :
    (UniformPriceFamily.model price).bundledProfit (UniformPriceFamily.model price).spec
        (UniformPriceFamily.strategy price) 1 ≤ model.bundledProfit model.spec strategy 1 :=
  le_of_lt (interior_profit_lt_boundary price)

end UniformBoundaryEquilibrium
end MathEconLib.Examples.AllPurchase
