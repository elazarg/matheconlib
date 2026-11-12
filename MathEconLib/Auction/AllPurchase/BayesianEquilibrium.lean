/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.BayesianEquilibrium
public import MathEconLib.Auction.AllPurchase.BayesianIntegrability
public import MathEconLib.Auction.AllPurchase.OriginalBidIC

/-!
# Bayesian equilibrium of interior all-purchase strategies

Original-bid interim incentives imply Bayesian Nash equilibrium in the actual
mechanism-induced game. Measurable bids monotone on bounded realized types
provide the integrability guards; the original type law supplies the prior.
The conclusion covers every measurable unilateral strategy change admitted by
the native payoff-integrability convention.
-/

@[expose] public section

namespace MathEconLib.LinearScarcityAuction

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {n : ℕ} [NeZero n] (A : LinearScarcityAuction Ω n)
  [A.HasIdenticalTypes] [A.HasBoundedTypes] [A.HasIndependentTypes]

/-- All-bid interim IC yields BNE when the common measurable strategy is
monotone on the bounded type interval. The actual model supplies every
payment and incumbent-integrability guard. -/
theorem isBNE_of_universalIC
    (β : ℝ → ℝ) (measurable : Measurable β)
    (monotone : MonotoneOn β (Icc A.lowestType A.highestType))
    (incentives : ∀ i, BidderProblem.HasUniversalIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β i) univ) :
    A.toAuction.bayesianGame.IsBNE A.typeLaw (A.toAuction.bidStrategy β measurable) := by
  have integrable (j : Fin n) : Integrable (fun sample => β (A.θ j sample)) ℙ :=
    A.toAuction.integrable_comp_type_of_monotoneOn β measurable monotone j
  exact A.toAuction.isBNE_of_universalIC A.spec.isUnitIntervalAllocation β measurable
    A.measurable_payment (A.integrable_payment_strat β integrable)
    (A.toAuction.incumbentPayoffsIntegrable_bidStrategy β measurable A.measurable_payment
      (A.integrable_realized_utility β measurable monotone)) incentives

/-- The supplied interior-strategy certificate is a native Bayesian Nash
equilibrium under the actual joint type law, including type-dependent deviations. -/
theorem IsInteriorRegimeStrategy.isBNE [n.AtLeastTwo] [A.HasAtomlessTypes]
    {β : ℝ → ℝ} {i : Fin n} (h : A.IsInteriorRegimeStrategy β i) :
    A.toAuction.bayesianGame.IsBNE A.typeLaw (A.toAuction.bidStrategy β h.measurable) :=
  A.isBNE_of_universalIC β h.measurable h.strictMonoOn.monotoneOn (h.hasUniversalIC_at A)

end MathEconLib.LinearScarcityAuction
