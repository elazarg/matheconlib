/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.Mechanism.Auctions.AllPurchase.WithPrice

/-!
# Changing the price of a linear-scarcity auction

The allocation, scarcity schedule and random bidder values are retained. Transfers use the new
posted price, so this construction changes the auction itself while preserving its type law.
-/

@[expose] public section

namespace MathEconLib.LinearScarcityAuction

open MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ} (A : LinearScarcityAuction Ω n)

/-- Replace the positive posted price, retaining scarcity, allocation and bidder values. -/
def withPrice (p : ℝ) (hp : 0 < p) : LinearScarcityAuction Ω n where
  toAuction := { A.toAuction with rules := A.spec.rulesAtPrice p }
  spec := A.spec.withPrice p hp
  φ_bar := A.φ_bar
  α_coeff := A.α_coeff
  α_pos := A.α_pos
  φ_bar_pos := A.φ_bar_pos
  scarcity_is_linear := A.scarcity_is_linear

@[simp] theorem withPrice_price (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).spec.price = p := rfl

@[simp] theorem withPrice_φ_bar (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).φ_bar = A.φ_bar := rfl

@[simp] theorem withPrice_α_coeff (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).α_coeff = A.α_coeff := rfl

@[simp] theorem withPrice_θ (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).θ = A.θ := rfl

@[simp] theorem withPrice_θmin (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).θmin = A.θmin := rfl

@[simp] theorem withPrice_θmax (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).θmax = A.θmax := rfl

@[simp] theorem withPrice_outcome (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).rules.outcome = A.rules.outcome := rfl

/-- Repricing preserves the actual joint type distribution. -/
@[simp] theorem withPrice_typeLaw (p : ℝ) (hp : 0 < p) :
    (A.withPrice p hp).typeLaw = A.typeLaw := rfl

instance (p : ℝ) (hp : 0 < p) [A.HasIndependentTypes] :
    (A.withPrice p hp).HasIndependentTypes where
  θ_indep := Auction.HasIndependentTypes.θ_indep (A := A.toAuction)

variable [NeZero n]

instance (p : ℝ) (hp : 0 < p) [A.HasIdenticalTypes] :
    (A.withPrice p hp).HasIdenticalTypes where
  θ_identical := Auction.HasIdenticalTypes.θ_identical (A := A.toAuction)
  θmin_eq := Auction.HasIdenticalTypes.θmin_eq (A := A.toAuction)
  θmax_eq := Auction.HasIdenticalTypes.θmax_eq (A := A.toAuction)

instance (p : ℝ) (hp : 0 < p) [A.HasBoundedTypes] :
    (A.withPrice p hp).HasBoundedTypes where
  θ_in := Auction.HasBoundedTypes.θ_in (A := A.toAuction)

instance (p : ℝ) (hp : 0 < p) [A.HasAtomlessTypes] :
    (A.withPrice p hp).HasAtomlessTypes where
  θ_noAtoms := Auction.HasAtomlessTypes.θ_noAtoms (A := A.toAuction)

@[simp] theorem withPrice_commonCDF [A.HasIdenticalTypes] (p : ℝ) (hp : 0 < p)
    (v : ℝ) : (A.withPrice p hp).commonCDF v = A.commonCDF v := rfl

end MathEconLib.LinearScarcityAuction
