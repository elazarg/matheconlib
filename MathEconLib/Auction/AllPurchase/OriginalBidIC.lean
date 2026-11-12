/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.AllPurchase.OptimalPricing
public import MathEconLib.Auction.AllPurchase.Regularity
public import MathEconLib.Auction.AllPurchase.QuadraticIncentives
public import MathEconLib.Auction.AllocationBounds

/-!
# Continuous all-purchase strategies and original-bid incentives

A continuous increasing strategy with a cost-minimizing lowest bid covers all
original real bids. Highest-bid allocation controls deviations outside the
report-generated bid interval. The interior all-pay formula supplies continuity
and the lowest-bid identity when an interior certificate is available.
-/

@[expose] public section

namespace MathEconLib.LinearScarcityAuction

open MeasureTheory ProbabilityTheory Set Real

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {n : ℕ} [NeZero n]

variable [n.AtLeastTwo] (A : LinearScarcityAuction Ω n)
variable [A.HasIdenticalTypes] [A.HasIndependentTypes]
variable [A.HasBoundedTypes] [A.HasAtomlessTypes]

/-- Continuous report coverage and a cost-minimizing lowest bid reject every original real bid.
The conditions apply independently of the sign of marginal net cost at zero. -/
theorem hasUniversalIC_of_continuous_strategy
    (β : ℝ → ℝ) (measurable : Measurable β)
    (strictMonoOn : StrictMonoOn β (Icc A.lowestType A.highestType))
    (continuous : ContinuousOn β (Icc A.lowestType A.highestType))
    (lowestBid : β A.lowestType = -(A.K_linear β) / (2 * A.α_coeff))
    (i : Fin n)
    (reportIC : BidderProblem.HasTypeDeviationIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β i)) :
    BidderProblem.HasUniversalIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β i) Set.univ := by
  have integrable (j : Fin n) : Integrable (fun sample => β (A.θ j sample)) ℙ :=
    A.toAuction.integrable_comp_type_of_monotoneOn β measurable strictMonoOn.monotoneOn j
  let P := A.toQuadraticCostProblem β measurable integrable i
  let : BidderProblem.HasTypeDeviationIC P.toBidderProblem := reportIC
  have lowEqual : P.lowestType = A.lowestType := A.θmin_eq_lowestType i
  have highEqual : P.highestType = A.highestType := A.θmax_eq_highestType i
  have intervalEqual : P.typeInterval = Icc A.lowestType A.highestType := by
    change Icc P.lowestType P.highestType = _
    rw [lowEqual, highEqual]
  apply P.hasUniversalIC_of_continuous_strategy
  · rw [lowEqual, highEqual]
    exact A.toAuction.lowestType_le_highestType
  · rw [intervalEqual]
    exact strictMonoOn.monotoneOn
  · rw [intervalEqual]
    exact continuous
  · rw [lowEqual]
    exact lowestBid
  · rw [lowEqual]
    exact A.toAuction.q_strat_eq_zero_of_le_lowest A.spec.usesStrictHighestBidAllocation
      strictMonoOn.monotoneOn i le_rfl
  · rw [highEqual]
    change A.q_strat β i (β A.highestType) = 1
    have member : A.highestType ∈ Icc A.lowestType A.highestType :=
      ⟨A.toAuction.lowestType_le_highestType, le_rfl⟩
    simpa only [Auction.commonCDF_highestType, one_pow] using
      A.toAuction.q_strat_at_strictMono_eq A.spec.usesStrictHighestBidAllocation
        strictMonoOn measurable i member
  · intro bid below
    rw [lowEqual] at below
    exact A.toAuction.q_strat_eq_zero_of_le_lowest A.spec.usesStrictHighestBidAllocation
      strictMonoOn.monotoneOn i below.le
  · intro bid above
    rw [highEqual] at above
    exact A.toAuction.q_strat_eq_one_of_highest_lt A.spec.usesStrictHighestBidAllocation
      strictMonoOn.monotoneOn i above

/-- Continuous nonnegative report coverage rejects every feasible nonnegative bid when
the lowest bid is zero and the marginal quadratic cost is nonnegative. -/
theorem hasUniversalIC_nonnegative_of_continuous_strategy
    (β : ℝ → ℝ) (measurable : Measurable β)
    (strictMonoOn : StrictMonoOn β (Icc A.lowestType A.highestType))
    (continuous : ContinuousOn β (Icc A.lowestType A.highestType))
    (lowestBid : β A.lowestType = 0) (marginal : 0 ≤ A.K_linear β)
    (i : Fin n)
    (reportIC : BidderProblem.HasTypeDeviationIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β i)) :
    BidderProblem.HasUniversalIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β i) (Ici 0) := by
  have integrable (j : Fin n) : Integrable (fun sample => β (A.θ j sample)) ℙ :=
    A.toAuction.integrable_comp_type_of_monotoneOn β measurable strictMonoOn.monotoneOn j
  let P := A.toQuadraticCostProblem β measurable integrable i
  let : BidderProblem.HasTypeDeviationIC P.toBidderProblem := reportIC
  have lowEqual : P.lowestType = A.lowestType := A.θmin_eq_lowestType i
  have highEqual : P.highestType = A.highestType := A.θmax_eq_highestType i
  have intervalEqual : P.typeInterval = Icc A.lowestType A.highestType := by
    change Icc P.lowestType P.highestType = _
    rw [lowEqual, highEqual]
  apply P.hasUniversalIC_nonnegative_of_continuous_strategy
  · rw [lowEqual, highEqual]
    exact A.toAuction.lowestType_le_highestType
  · rw [intervalEqual]
    exact strictMonoOn.monotoneOn
  · rw [intervalEqual]
    exact continuous
  · rw [lowEqual]
    exact lowestBid
  · exact marginal
  · rw [highEqual]
    change A.q_strat β i (β A.highestType) = 1
    have member : A.highestType ∈ Icc A.lowestType A.highestType :=
      ⟨A.toAuction.lowestType_le_highestType, le_rfl⟩
    simpa only [Auction.commonCDF_highestType, one_pow] using
      A.toAuction.q_strat_at_strictMono_eq A.spec.usesStrictHighestBidAllocation
        strictMonoOn measurable i member
  · intro bid above
    rw [highEqual] at above
    exact A.toAuction.q_strat_eq_one_of_highest_lt A.spec.usesStrictHighestBidAllocation
      strictMonoOn.monotoneOn i above

/-- The native interior formula makes the prescribed strategy continuous on its type interval. -/
theorem IsInteriorRegimeStrategy.continuousOn {β : ℝ → ℝ} {i : Fin n}
    (h : A.IsInteriorRegimeStrategy β i) :
    ContinuousOn β (Icc A.lowestType A.highestType) := by
  have formulaContinuous : Continuous (fun value => -(A.K_linear β) / (2 * A.α_coeff) +
      sqrt (A.toAuction.allPayBid value) / sqrt A.α_coeff) :=
    continuous_const.add
      ((Real.continuous_sqrt.comp A.toAuction.allPayBid_continuous).div_const _)
  exact formulaContinuous.continuousOn.congr
    (fun value member => A.interior_regime_strategy_eq_allPayBid β i h value member)

/-- The lowest prescribed bid equals the vertex of the quadratic cost. -/
theorem IsInteriorRegimeStrategy.lowestType_eq_vertex {β : ℝ → ℝ} {i : Fin n}
    (h : A.IsInteriorRegimeStrategy β i) :
    β A.lowestType = -(A.K_linear β) / (2 * A.α_coeff) := by
  have member : A.lowestType ∈ Icc A.lowestType A.highestType :=
    ⟨le_rfl, A.toAuction.lowestType_le_highestType⟩
  simpa only [Auction.allPayBid_lowestType, Real.sqrt_zero, zero_div, add_zero] using
    A.interior_regime_strategy_eq_allPayBid β i h A.lowestType member

omit [A.HasIndependentTypes] [A.HasAtomlessTypes] in
/-- The lowest prescribed bid has zero winning probability. -/
theorem IsInteriorRegimeStrategy.q_strat_lowestType {β : ℝ → ℝ} {i : Fin n}
    (h : A.IsInteriorRegimeStrategy β i) :
    A.toAuction.q_strat β i (β A.lowestType) = 0 := by
  exact A.toAuction.q_strat_eq_zero_of_le_lowest A.spec.usesStrictHighestBidAllocation
    h.strictMonoOn.monotoneOn i le_rfl

omit [n.AtLeastTwo] in
/-- The highest prescribed bid has winning probability one under atomless types. -/
theorem IsInteriorRegimeStrategy.q_strat_highestType {β : ℝ → ℝ} {i : Fin n}
    (h : A.IsInteriorRegimeStrategy β i) :
    A.toAuction.q_strat β i (β A.highestType) = 1 := by
  have member : A.highestType ∈ Icc A.lowestType A.highestType :=
    ⟨A.toAuction.lowestType_le_highestType, le_rfl⟩
  simpa only [Auction.commonCDF_highestType, one_pow] using
    A.toAuction.q_strat_at_strictMono_eq A.spec.usesStrictHighestBidAllocation
      h.strictMonoOn h.measurable i member

/-- Interior report incentives reject every original real bid. Strategy continuity,
the cost-minimizing lowest bid and endpoint allocation bounds follow from the
existing interior assumptions rather than additional hypotheses. -/
theorem IsInteriorRegimeStrategy.hasUniversalIC {β : ℝ → ℝ} {i : Fin n}
    (h : A.IsInteriorRegimeStrategy β i) :
    BidderProblem.HasUniversalIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β i) Set.univ :=
  A.hasUniversalIC_of_continuous_strategy β h.measurable h.strictMonoOn
    (h.continuousOn A) (h.lowestType_eq_vertex A) i h.typeDeviationIC

/-- Identical independent bidders face the same interim allocation and quadratic cost. -/
theorem interimPayoff_eq (β : ℝ → ℝ)
    (monotone : MonotoneOn β (Icc A.lowestType A.highestType)) (measurable : Measurable β)
    (integrable : ∀ j, Integrable (fun ω => β (A.θ j ω)) ℙ)
    (i j : Fin n) (v bid : ℝ) :
    (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).payoff v bid =
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β j).payoff v bid := by
  change v * A.q_strat β i bid - A.p_strat β i bid =
    v * A.q_strat β j bid - A.p_strat β j bid
  rw [A.toAuction.q_strat_eq_cdf_pow A.spec.usesStrictHighestBidAllocation monotone measurable i,
    A.toAuction.q_strat_eq_cdf_pow A.spec.usesStrictHighestBidAllocation monotone measurable j,
    A.p_strat_eq_quadratic β measurable integrable i,
    A.p_strat_eq_quadratic β measurable integrable j]

/-- A representative interior incentive certificate certifies every identical bidder
against every real original bid. -/
theorem IsInteriorRegimeStrategy.hasUniversalIC_at {β : ℝ → ℝ} {i : Fin n}
    (h : A.IsInteriorRegimeStrategy β i) (j : Fin n) :
    BidderProblem.HasUniversalIC
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β j) Set.univ where
  strategyInS _ _ := Set.mem_univ _
  universalIC v member bid _ := by
    have originalMember : v ∈ Icc (A.θmin i) (A.θmax i) := by
      change v ∈ Icc (A.θmin j) (A.θmax j) at member
      simpa only [A.θmin_eq_lowestType, A.θmax_eq_highestType] using member
    have comparison := (h.hasUniversalIC A).universalIC v originalMember bid (Set.mem_univ _)
    change (A.toBidderProblem A.spec.isUnitIntervalAllocation β j).payoff v bid ≤
      (A.toBidderProblem A.spec.isUnitIntervalAllocation β j).payoff v (β v)
    calc
      _ = (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).payoff v bid :=
        A.interimPayoff_eq β h.strictMonoOn.monotoneOn h.measurable h.integrable j i v bid
      _ ≤ (A.toBidderProblem A.spec.isUnitIntervalAllocation β i).payoff v (β v) := comparison
      _ = _ :=
        A.interimPayoff_eq β h.strictMonoOn.monotoneOn h.measurable h.integrable i j v (β v)

end MathEconLib.LinearScarcityAuction
