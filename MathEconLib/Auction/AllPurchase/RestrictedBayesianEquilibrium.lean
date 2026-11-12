/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.RestrictedBayesianEquilibrium
public import MathEconLib.Auction.AllPurchase.BayesianIntegrability
public import Mathlib.Basic.NNReal.Basic

/-!
# Nonnegative-bid Bayesian equilibrium of linear-scarcity auctions

A measurable nonnegative strategy monotone on the bounded type interval supplies
the native payment and incumbent-integrability guards. Interim IC on nonnegative
real bids then implies Bayesian equilibrium in the actual action-restricted game,
under the auction's original type law. No conclusion for unrestricted real bids
is inferred, and the original auction data retain their real bid carrier.
-/

@[expose] public noncomputable section

namespace MathEconLib.LinearScarcityAuction

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n : ℕ} [NeZero n] (A : LinearScarcityAuction Ω n)
    [A.HasIdenticalTypes] [A.HasBoundedTypes] [A.HasIndependentTypes]

/-- Native nonnegative-action equilibrium from IC, with integrability supplied by the auction. -/
theorem isBNE_nonnegative_of_universalIC
    (β : ℝ → ℝ≥0) (measurable : Measurable β)
    (monotone : MonotoneOn (fun v => (β v : ℝ)) (Icc A.lowestType A.highestType))
    (incentives : ∀ i, BidderProblem.HasUniversalIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation (fun v => (β v : ℝ)) i) (Ici 0)) :
    (A.toAuction.bayesianGame.comapActions (fun _ => (Subtype.val : ℝ≥0 → ℝ))).IsBNE
      A.typeLaw (A.toAuction.restrictedBidStrategy (Ici 0) β measurable) := by
  have realMeasurable : Measurable (fun v => (β v : ℝ)) :=
    measurable_subtype_coe.comp measurable
  have integrable (j : Fin n) :
      Integrable (fun sample => (β (A.θ j sample) : ℝ)) ℙ :=
    A.toAuction.integrable_comp_type_of_monotoneOn (fun v => (β v : ℝ))
      realMeasurable monotone j
  exact A.toAuction.isBNE_restricted_of_universalIC A.spec.isUnitIntervalAllocation
    (Ici 0) β measurable A.measurable_payment
    (A.integrable_payment_strat (fun v => (β v : ℝ)) integrable)
    (A.integrable_realized_utility (fun v => (β v : ℝ)) realMeasurable monotone) incentives

end MathEconLib.LinearScarcityAuction
