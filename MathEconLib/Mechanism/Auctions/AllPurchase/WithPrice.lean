/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism.Auctions.AllPurchase.Spec

/-!
# Changing an all-purchase posted price

Changing the posted price retains the allocation and scarcity schedule and replaces the signed
transfers. Positivity is needed for the resulting all-purchase specification, not for the rule.
-/

@[expose] public section

namespace MathEconLib.Mechanism.Auctions.AllPurchaseSpec

variable {I O : Type*} [Fintype I]
variable {M : Mechanism I (fun _ => ℝ) O} {alloc : O → I → ℝ}

/-- The same allocation rule, with transfers at a new posted price. -/
def rulesAtPrice (spec : AllPurchaseSpec M alloc) (p : ℝ) :
    Mechanism I (fun _ => ℝ) O where
  outcome := M.outcome
  transfer i bids := -((p - spec.φ (∑ j, bids j)) * bids i)

/-- A positive new price, retaining the original scarcity schedule and prize rule. -/
def withPrice (spec : AllPurchaseSpec M alloc) (p : ℝ) (hp : 0 < p) :
    AllPurchaseSpec (spec.rulesAtPrice p) alloc where
  price := p
  price_pos := hp
  φ := spec.φ
  φ_continuous := spec.φ_continuous
  φ_strictAnti := spec.φ_strictAnti
  usesStrictHighestBidAllocation := spec.usesStrictHighestBidAllocation
  transfer_eq _ _ := rfl

/-- Changing price changes each payment by the price difference times own purchases. -/
theorem payment_rulesAtPrice (spec : AllPurchaseSpec M alloc) (p : ℝ) (i : I)
    (bids : I → ℝ) :
    (spec.rulesAtPrice p).payment i bids =
      M.payment i bids + (p - spec.price) * bids i := by
  rw [spec.payment_eq]
  simp only [Mechanism.payment, rulesAtPrice, neg_neg]
  ring

/-- Reinstating the original price recovers the original mechanism. -/
@[simp] theorem rulesAtPrice_price (spec : AllPurchaseSpec M alloc) :
    spec.rulesAtPrice spec.price = M := by
  refine Mechanism.ext ?_ ?_
  · rfl
  · funext i bids
    exact (spec.transfer_eq i bids).symm

end MathEconLib.Mechanism.Auctions.AllPurchaseSpec
