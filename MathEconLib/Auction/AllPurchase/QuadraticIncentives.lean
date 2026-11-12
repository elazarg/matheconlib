/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import MathEconLib.BidderProblem.UniversalIC
public import MathEconLib.SingleParameter.ActionCoverage
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Payoff coverage for quadratic-cost bidders

A continuous monotone strategy covers its endpoint bid interval. When
the lowest bid minimizes quadratic cost and endpoint winning probabilities
agree with the probabilities outside the range, endpoint bids also cover
every outside bid. Coverage is valid at every real true type.
-/

@[expose] public section

namespace MathEconLib.QuadraticCostProblem

open Set


/-- Every real bid is dominated by a report when endpoints and outside winning
probabilities agree, and the lowest bid is the quadratic cost minimizer. -/
theorem payoff_dominated_by_report (P : QuadraticCostProblem)
    (ordered : P.lowestType ≤ P.highestType)
    (monotone : MonotoneOn P.strategy P.typeInterval)
    (continuous : ContinuousOn P.strategy P.typeInterval)
    (lowestBid : P.strategy P.lowestType = -P.K_param / (2 * P.α_coeff))
    (winLowest : P.winProb (P.strategy P.lowestType) = 0)
    (winHighest : P.winProb (P.strategy P.highestType) = 1)
    (winBelow : ∀ bid < P.strategy P.lowestType, P.winProb bid = 0)
    (winAbove : ∀ bid > P.strategy P.highestType, P.winProb bid = 1)
    (v bid : ℝ) :
    ∃ report ∈ P.typeInterval,
      P.payoff v bid ≤ P.payoff v (P.strategy report) := by
  have lowMember : P.lowestType ∈ P.typeInterval := ⟨le_rfl, ordered⟩
  have highMember : P.highestType ∈ P.typeInterval := ⟨ordered, le_rfl⟩
  have endpointOrder := monotone lowMember highMember ordered
  have denominator : 2 * P.α_coeff ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) P.α_pos)
  have stationary : P.K_param = -(2 * P.α_coeff) * P.strategy P.lowestType := by
    have equality := (eq_div_iff denominator).mp lowestBid
    nlinarith
  have costMinimum (b : ℝ) : P.cost (P.strategy P.lowestType) ≤ P.cost b := by
    have square := mul_nonneg P.α_pos.le (sq_nonneg (b - P.strategy P.lowestType))
    simp only [P.cost_eq, stationary]
    nlinarith [square]
  have costAbove (b : ℝ) (above : P.strategy P.highestType ≤ b) :
      P.cost (P.strategy P.highestType) ≤ P.cost b := by
    have sumNonnegative : 0 ≤ b + P.strategy P.highestType - 2 * P.strategy P.lowestType := by
      linarith
    have product := mul_nonneg P.α_pos.le
      (mul_nonneg (sub_nonneg.mpr above) sumNonnegative)
    simp only [P.cost_eq, stationary]
    nlinarith [product]
  by_cases below : bid < P.strategy P.lowestType
  · refine ⟨P.lowestType, lowMember, ?_⟩
    simp only [BidderProblem.payoff, winBelow bid below, winLowest, mul_zero, zero_sub]
    exact neg_le_neg (costMinimum bid)
  by_cases above : P.strategy P.highestType < bid
  · refine ⟨P.highestType, highMember, ?_⟩
    simp only [BidderProblem.payoff, winAbove bid above, winHighest, mul_one]
    exact sub_le_sub_left (costAbove bid above.le) v
  have between : bid ∈ Icc (P.strategy P.lowestType) (P.strategy P.highestType) :=
    ⟨le_of_not_gt below, le_of_not_gt above⟩
  obtain ⟨report, validReport, sameBid⟩ := intermediate_value_Icc ordered continuous between
  refine ⟨report, validReport, ?_⟩
  simpa only [sameBid] using le_refl (P.payoff v bid)

/-- Continuous report coverage and endpoint cost bounds upgrade report IC to
universal original-bid IC, including negative bids. -/
theorem hasUniversalIC_of_continuous_strategy (P : QuadraticCostProblem)
    [BidderProblem.HasTypeDeviationIC P.toBidderProblem]
    (ordered : P.lowestType ≤ P.highestType)
    (monotone : MonotoneOn P.strategy P.typeInterval)
    (continuous : ContinuousOn P.strategy P.typeInterval)
    (lowestBid : P.strategy P.lowestType = -P.K_param / (2 * P.α_coeff))
    (winLowest : P.winProb (P.strategy P.lowestType) = 0)
    (winHighest : P.winProb (P.strategy P.highestType) = 1)
    (winBelow : ∀ bid < P.strategy P.lowestType, P.winProb bid = 0)
    (winAbove : ∀ bid > P.strategy P.highestType, P.winProb bid = 1) :
    BidderProblem.HasUniversalIC P.toBidderProblem Set.univ := by
  have typeIC : SingleParameterProblem.HasTypeDeviationIC
      P.toBidderProblem.toSingleParameterProblem := inferInstance
  apply BidderProblem.hasUniversalIC_of_toSingleParameterProblem
  refine typeIC.hasUniversalIC_of_payoff_coverage (fun _ _ => Set.mem_univ _) ?_
  intro v _ bid _
  exact P.payoff_dominated_by_report ordered monotone continuous lowestBid
    winLowest winHighest winBelow winAbove v bid

end MathEconLib.QuadraticCostProblem
