/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.UniformTwoBidder
public import Mathlib.Tactic.NormNum

/-!
# Native Bayesian payoffs for two uniform bidders

The equilibrium's actual ex-ante quasilinear utility is `13/36` for each
bidder. The native Bayesian equilibrium bounds every admitted measurable
unilateral strategy deviation by the same value. Interim averaging and the
already established uniform second moment supply the numerical evaluation.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase.UniformTwoBidder

open MeasureTheory ProbabilityTheory Set GameTheory
open GameTheory.BayesianPrior UniformProbability

/-- The native conditional payoff equals the already computed interim utility. -/
theorem strategy_interimPayoff (i : Fin 2) (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    model.toAuction.bayesianGame.interimPayoff model.typeLaw model.toAuction.independentBeliefs
      i v (model.toAuction.bidStrategy strategy strategy_measurable) = v ^ 2 / 4 + 1 / 36 := by
  change model.toAuction.bayesianGame.interimPayoffAction model.typeLaw
    model.toAuction.independentBeliefs i v (strategy v)
      (model.toAuction.bidStrategy strategy strategy_measurable) = _
  rw [model.toAuction.interimPayoffAction_bidStrategy model.spec.isUnitIntervalAllocation
    strategy strategy_measurable model.measurable_payment
    (model.integrable_payment_strat strategy strategy_integrable)]
  exact utility_eq i v member

/-- This is the actual prior expectation, including both prize value and signed transfers. -/
theorem strategy_exAntePayoff (i : Fin 2) :
    model.toAuction.bayesianGame.exAntePayoff model.typeLaw i
      (model.toAuction.bidStrategy strategy strategy_measurable) = 13 / 36 := by
  rw [model.toAuction.bayesianGame.exAntePayoff_eq_integral_interimPayoff model.typeLaw
    model.toAuction.independentBeliefs
    (model.toAuction.measurable_bayesianGame_payoff model.measurable_payment) i
    (model.toAuction.bidStrategy strategy strategy_measurable) (strategy_isBNE.integrable i)]
  have marginal : marginalType model.typeLaw i = Measure.map (value i) ℙ := by
    unfold marginalType Auction.typeLaw
    rw [Measure.map_map (measurable_pi_apply i)
      (Measurable.of_eval model.θ_measurable)]
    rfl
  rw [marginal, integral_map (measurable_value i).aemeasurable
    (model.toAuction.bayesianGame.measurable_interimPayoff model.typeLaw
      model.toAuction.independentBeliefs
      (model.toAuction.measurable_bayesianGame_payoff model.measurable_payment) i
      (model.toAuction.bidStrategy strategy strategy_measurable)).aestronglyMeasurable]
  have realized (sample : Ω) :
      model.toAuction.bayesianGame.interimPayoff model.typeLaw model.toAuction.independentBeliefs
          i (value i sample) (model.toAuction.bidStrategy strategy strategy_measurable) =
        value i sample ^ 2 / 4 + 1 / 36 :=
    strategy_interimPayoff i _ (value_mem i sample)
  simp_rw [realized]
  rw [integral_add ((integrable_value_sq i).div_const 4) (integrable_const _),
    integral_div 4 (fun sample => value i sample ^ 2), integral_value_sq,
    integral_const, probReal_univ, one_smul]
  norm_num

/-- Full measurable type-dependent deviations are bounded under the native integrability guard. -/
theorem unilateral_exAntePayoff_le (i : Fin 2)
    (alternative : model.toAuction.bayesianGame.Strategy)
    (opponents : ∀ j, j ≠ i → alternative j =
      model.toAuction.bidStrategy strategy strategy_measurable j)
    (integrable : Integrable (fun types => model.toAuction.bayesianGame.payoff i
      (model.toAuction.bayesianGame.measurableActionProfile alternative types) types)
        model.typeLaw) :
    model.toAuction.bayesianGame.exAntePayoff model.typeLaw i alternative ≤ 13 / 36 := by
  have bound : model.toAuction.bayesianGame.exAntePayoff model.typeLaw i alternative ≤
      model.toAuction.bayesianGame.exAntePayoff model.typeLaw i
        (model.toAuction.bidStrategy strategy strategy_measurable) :=
    strategy_isBNE.deviation_le i alternative ⟨opponents, integrable⟩
  rwa [strategy_exAntePayoff] at bound

end MathEconLib.Examples.AllPurchase.UniformTwoBidder
