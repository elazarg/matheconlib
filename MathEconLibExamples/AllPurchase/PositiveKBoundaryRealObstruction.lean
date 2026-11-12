/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.PositiveKBoundary
public import MathEconLib.Auction.AllPurchase.BayesianIntegrability
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.InterimConverse
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# A positive-mass original-bid obstruction in the uniform boundary model

The prescribed boundary strategy fails native Bayesian equilibrium in the real-action
auction. Its negative
fixed bid yields utility one quarter at every true type, exceeding prescribed
utility throughout a positive-mass interval of the original uniform prior.
The native interim converse performs the ex-ante-to-conditional step, protected
by simultaneous conditional integrability for all actions. This conclusion does
not infer ex-ante failure from a comparison at a single null type.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase.PositiveKBoundary

open MeasureTheory ProbabilityTheory Set MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior UniformProbability

/-- The original real-action strategy fails actual Bayesian Nash equilibrium under its type law. -/
theorem strategy_not_real_isBNE :
    ¬ model.toAuction.bayesianGame.IsBNE model.typeLaw
      (model.toAuction.bidStrategy strategy strategy_measurable) := by
  intro equilibrium
  have payments := model.measurable_payment
  have integrablePayments := model.integrable_payment_strat strategy strategy_integrable
  have conditional := model.toAuction.hasIntegrableInterimDeviations_bidStrategy
    model.spec.isUnitIntervalAllocation strategy strategy_measurable payments integrablePayments
  have optimal := model.toAuction.bayesianGame.ae_interim_of_isBNE model.typeLaw
    model.independentBeliefs (model.toAuction.measurable_bayesianGame_payoff payments)
    (model.toAuction.bidStrategy strategy strategy_measurable) equilibrium conditional
  have marginal : marginalType model.typeLaw (0 : Fin 2) = Measure.map (value 0) ℙ := by
    unfold marginalType Auction.typeLaw
    rw [Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval model.θ_measurable)]
    rfl
  have mass : marginalType model.typeLaw (0 : Fin 2) (Iic (1 / 2 : ℝ)) ≠ 0 := by
    rw [marginal, ← ofReal_cdf (Measure.map (value 0) ℙ),
      cdf_value 0 (1 / 2) (by norm_num)]
    norm_num
  have bounded : ∀ᵐ v ∂(marginalType model.typeLaw (0 : Fin 2)), v ∈ Icc (0 : ℝ) 2 :=
    mem_ae_iff.mpr (model.toAuction.marginalType_interval_compl 0)
  have visits : ∃ᵐ v ∂(marginalType model.typeLaw (0 : Fin 2)), v ∈ Iic (1 / 2 : ℝ) :=
    frequently_ae_mem_iff.mpr mass
  obtain ⟨v, ⟨upper, member⟩, comparison⟩ :=
    ((visits.and_eventually bounded).and_eventually (optimal 0)).exists
  have bad := comparison (-(1 / 2))
  change model.toAuction.bayesianGame.interimPayoffAction model.typeLaw
      model.independentBeliefs 0 v (-(1 / 2))
        (model.toAuction.bidStrategy strategy strategy_measurable) ≤
    model.toAuction.bayesianGame.interimPayoffAction model.typeLaw
      model.independentBeliefs 0 v (strategy v)
        (model.toAuction.bidStrategy strategy strategy_measurable) at bad
  rw [model.toAuction.interimPayoffAction_bidStrategy model.spec.isUnitIntervalAllocation
      strategy strategy_measurable payments integrablePayments,
    model.toAuction.interimPayoffAction_bidStrategy model.spec.isUnitIntervalAllocation
      strategy strategy_measurable payments integrablePayments] at bad
  change (problem 0).payoff v (-(1 / 2)) ≤ (problem 0).U v at bad
  rw [negative_payoff, utility_eq 0 v member] at bad
  have nonnegative : 0 ≤ v := member.1
  have upperBound : v ≤ 1 / 2 := upper
  nlinarith [mul_nonneg nonnegative (sub_nonneg.mpr upperBound)]

end MathEconLib.Examples.AllPurchase.PositiveKBoundary
