/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.UniformPriceFamily
public import MathEconLib.Auction.AllPurchase.EquilibriumPriceComparison

/-!
# Actual equilibrium profit along the uniform price family

The price-indexed mechanisms retain the original value law and scarcity rule.
Their already certified interior equilibria have aggregate quantity
`2 * (4 - p) / 3` and actual seller profit `2 * p * (4 - p) / 3` at zero cost.
The native two-auction comparison identifies price two as the unique optimum
within this family, with square profit gap `2/3 * (p - 2)^2`.
No claim is made about another equilibrium regime or production cost.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase.UniformPriceFamily

open MeasureTheory ProbabilityTheory Set
open UniformProbability

/-- Repricing preserves the actual distribution-based all-pay moment. -/
theorem expectedSqrtAllPayBid_eq (price : Price) :
    (model price).toAuction.expectedSqrtAllPayBid = 1 / 2 :=
  UniformTwoBidder.expectedSqrtAllPayBid_eq

/-- Native interior quantity evaluated at each actual posted price. -/
theorem expectedAggregateBid_eq (price : Price) :
    (model price).expectedAggregateBid (strategy price) = 2 * (4 - price.val) / 3 := by
  rw [(model price).expectedAggregateBid_eq_interiorMeanQuantity
    (strategy price) (interior_strategy price), expectedSqrtAllPayBid_eq]
  change MathEconLib.AllPurchase.interiorMeanQuantity 3 1 (1 / 2) 2 price.val = _
  norm_num [MathEconLib.AllPurchase.interiorMeanQuantity]
  ring

/-- Native bundled profit evaluated at the equilibrium of the repriced mechanism. -/
theorem bundledProfit_eq (price : Price) :
    (model price).bundledProfit (model price).spec (strategy price) 0 =
      2 * price.val * (4 - price.val) / 3 := by
  rw [(model price).bundledProfit_eq_sellerProfitInterior
    (strategy price) (interior_strategy price) 0, expectedSqrtAllPayBid_eq]
  change MathEconLib.AllPurchase.sellerProfitInterior 3 1 0 (1 / 2) 2 price.val = _
  norm_num [MathEconLib.AllPurchase.sellerProfitInterior,
    MathEconLib.AllPurchase.interiorMeanQuantity]
  ring

/-- The profit-maximizing member of the constructed zero-cost interior family. -/
def optimalPrice : Price := ⟨2, by norm_num⟩

theorem model_optimalPrice_eq_uniformTwoBidder :
    model optimalPrice = UniformTwoBidder.model := rfl

theorem strategy_optimalPrice_eq_uniformTwoBidder :
    strategy optimalPrice = UniformTwoBidder.strategy := by
  funext value
  dsimp only [strategy, baseline, optimalPrice, UniformTwoBidder.strategy]
  ring

/-- The second supplied auction is posted at the common interior optimum. -/
theorem optimalPrice_actual (price : Price) :
    (model optimalPrice).spec.price = MathEconLib.AllPurchase.optimalPriceInterior
      (model price).φ_bar 0 (model price).α_coeff
      (model price).toAuction.expectedSqrtAllPayBid := by
  rw [expectedSqrtAllPayBid_eq]
  change (2 : ℝ) = MathEconLib.AllPurchase.optimalPriceInterior 3 0 1 (1 / 2)
  norm_num [MathEconLib.AllPurchase.optimalPriceInterior]

/-- The exact gap compares two actual mechanisms with their respective equilibrium strategies. -/
theorem bundledProfit_sub_eq (price : Price) :
    (model optimalPrice).bundledProfit (model optimalPrice).spec (strategy optimalPrice) 0 -
        (model price).bundledProfit (model price).spec (strategy price) 0 =
      (2 / 3 : ℝ) * (price.val - 2) ^ 2 := by
  have gap := (model price).bundledProfit_sub_eq_sq_of_optimal_price
    (model optimalPrice) (strategy price) (strategy optimalPrice)
    (interior_strategy price) (interior_strategy optimalPrice)
    rfl rfl rfl 0 (optimalPrice_actual price)
  change _ = ((2 : ℝ) / (1 * (2 + 1))) * (price.val - 2) ^ 2 at gap
  norm_num at gap
  exact gap

/-- The actual equilibrium auction at price two dominates every member of the family. -/
theorem bundledProfit_le_optimal (price : Price) :
    (model price).bundledProfit (model price).spec (strategy price) 0 ≤
      (model optimalPrice).bundledProfit (model optimalPrice).spec (strategy optimalPrice) 0 :=
  (model price).bundledProfit_le_of_optimal_price
    (model optimalPrice) (strategy price) (strategy optimalPrice)
    (interior_strategy price) (interior_strategy optimalPrice)
    rfl rfl rfl 0 (optimalPrice_actual price)

/-- The native actual-auction equality criterion identifies the unique price. -/
theorem bundledProfit_eq_iff_optimal (price : Price) :
    (model price).bundledProfit (model price).spec (strategy price) 0 =
        (model optimalPrice).bundledProfit (model optimalPrice).spec (strategy optimalPrice) 0 ↔
      price.val = 2 :=
  (model price).bundledProfit_eq_iff_price_eq_of_optimal_price
    (model optimalPrice) (strategy price) (strategy optimalPrice)
    (interior_strategy price) (interior_strategy optimalPrice)
    rfl rfl rfl 0 (optimalPrice_actual price)

theorem bundledProfit_optimalPrice_eq :
    (model optimalPrice).bundledProfit (model optimalPrice).spec (strategy optimalPrice) 0 =
      8 / 3 := by
  rw [bundledProfit_eq]
  norm_num [optimalPrice]

theorem bundledProfit_gap_eq (price : Price) :
    8 / 3 - (model price).bundledProfit (model price).spec (strategy price) 0 =
      (2 / 3 : ℝ) * (price.val - 2) ^ 2 := by
  rw [← bundledProfit_optimalPrice_eq]
  exact bundledProfit_sub_eq price

theorem bundledProfit_le (price : Price) :
    (model price).bundledProfit (model price).spec (strategy price) 0 ≤ 8 / 3 := by
  rw [← bundledProfit_optimalPrice_eq]
  exact bundledProfit_le_optimal price

theorem bundledProfit_eq_max_iff (price : Price) :
    (model price).bundledProfit (model price).spec (strategy price) 0 = 8 / 3 ↔ price.val = 2 := by
  rw [← bundledProfit_optimalPrice_eq]
  exact bundledProfit_eq_iff_optimal price

end MathEconLib.Examples.AllPurchase.UniformPriceFamily
