/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.AllPurchase.OptimalPricing

/-!
# Profit comparisons between actual interior auctions

Two supplied auctions share the scarcity intercept, scarcity slope, bidder count
and square-root all-pay moment. If the second auction's actual posted price is
the common interior optimum, its actual bundled profit dominates the first,
with an exact square gap and equality precisely at equal posted prices.
The strategies and their interior certificates are inputs. No auction or
equilibrium is constructed at another price, and no other regime is compared.
-/

namespace MathEconLib

@[expose] public section

open MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {n : ℕ} [NeZero n] [n.AtLeastTwo]

namespace LinearScarcityAuction

variable (A B : LinearScarcityAuction Ω n)
  [A.HasIdenticalTypes] [A.HasIndependentTypes] [A.HasBoundedTypes] [A.HasAtomlessTypes]
  [B.HasIdenticalTypes] [B.HasIndependentTypes] [B.HasBoundedTypes] [B.HasAtomlessTypes]
  (firstStrategy secondStrategy : ℝ → ℝ)
  (firstInterior : A.IsInteriorRegimeStrategy firstStrategy 0)
  (secondInterior : B.IsInteriorRegimeStrategy secondStrategy 0)
  (sameIntercept : B.φ_bar = A.φ_bar)
  (sameSlope : B.α_coeff = A.α_coeff)
  (sameMoment : B.toAuction.expectedSqrtAllPayBid = A.toAuction.expectedSqrtAllPayBid)
  (cost : ℝ)
  (optimalPrice : B.spec.price = AllPurchase.optimalPriceInterior A.φ_bar cost A.α_coeff
    A.toAuction.expectedSqrtAllPayBid)

include firstInterior secondInterior sameIntercept sameSlope sameMoment optimalPrice

/-- The exact square gap compares the profits of the two supplied auction strategies. -/
theorem bundledProfit_sub_eq_sq_of_optimal_price :
    B.toAuction.bundledProfit B.spec secondStrategy cost -
        A.toAuction.bundledProfit A.spec firstStrategy cost =
      ((n : ℝ) / (A.α_coeff * ((n : ℝ) + 1))) *
        (A.spec.price - B.spec.price) ^ 2 := by
  rw [A.bundledProfit_eq_sellerProfitInterior firstStrategy firstInterior cost,
    B.bundledProfit_eq_sellerProfitInterior secondStrategy secondInterior cost,
    sameIntercept, sameSlope, sameMoment, optimalPrice]
  exact AllPurchase.sellerProfitInterior_optimal_sub A.α_pos
    (by have := Nat.AtLeastTwo.prop (n := n); omega) A.spec.price

/-- The actual auction at the common optimum dominates the supplied interior comparator. -/
theorem bundledProfit_le_of_optimal_price :
    A.toAuction.bundledProfit A.spec firstStrategy cost ≤
      B.toAuction.bundledProfit B.spec secondStrategy cost := by
  rw [A.bundledProfit_eq_sellerProfitInterior firstStrategy firstInterior cost,
    B.bundledProfit_eq_sellerProfitInterior secondStrategy secondInterior cost,
    sameIntercept, sameSlope, sameMoment, optimalPrice]
  exact AllPurchase.sellerProfitInterior_le_at_optimal A.α_pos
    (by have := Nat.AtLeastTwo.prop (n := n); omega) A.spec.price

/-- Equality of actual profits holds exactly when their posted prices coincide. -/
theorem bundledProfit_eq_iff_price_eq_of_optimal_price :
    A.toAuction.bundledProfit A.spec firstStrategy cost =
        B.toAuction.bundledProfit B.spec secondStrategy cost ↔
      A.spec.price = B.spec.price := by
  rw [A.bundledProfit_eq_sellerProfitInterior firstStrategy firstInterior cost,
    B.bundledProfit_eq_sellerProfitInterior secondStrategy secondInterior cost,
    sameIntercept, sameSlope, sameMoment, optimalPrice]
  exact AllPurchase.sellerProfitInterior_eq_at_optimal_iff A.α_pos
    (by have := Nat.AtLeastTwo.prop (n := n); omega) A.spec.price

end LinearScarcityAuction

end

end MathEconLib
