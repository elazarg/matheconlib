/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.Typeclasses
public import MathEconLib.BidderProblem.UniversalIC
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Interim

/-!
# Bayesian equilibrium from the actual interim bidder problems

The auction's scalar private-value environment induces the native Bayesian game
on its actual joint type law. Under independence, a conditional action payoff
is the existing allocation/payment expression against the common bid strategy.
Universal interim optimality on the declared type intervals then supplies a
Bayesian Nash equilibrium through the native averaging theorem. Payment
measurability, fixed-bid integrability and incumbent integrability remain explicit.
-/

namespace MathEconLib

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior
open MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n : ℕ}

namespace Auction

variable (A : Auction Ω n)

/-- The Bayesian game induced by the auction's actual allocation and signed transfers. -/
abbrev bayesianGame := A.rules.inducedBayesianGame (valuationEnvironment n)

/-- Each bidder uses the same measurable strategy on its own private value. -/
def bidStrategy (β : ℝ → ℝ) (measurable : Measurable β) : A.bayesianGame.Strategy :=
  fun _ => ⟨β, measurable⟩

@[simp] theorem bayesianGame_payoff (i : Fin n) (bids types : Fin n → ℝ) :
    A.bayesianGame.payoff i bids types =
      types i * A.rules.outcome bids i - A.rules.payment i bids := by
  change types i * A.rules.outcome bids i + A.rules.transfer i bids =
    types i * A.rules.outcome bids i - (-A.rules.transfer i bids)
  simp

/-- Raw payment measurability supplies joint measurability of the induced private-value payoff. -/
theorem measurable_bayesianGame_payoff
    (payments : ∀ i, Measurable (A.rules.payment i)) (i : Fin n) :
    Measurable (fun point : (Fin n → ℝ) × (Fin n → ℝ) =>
      A.bayesianGame.payoff i point.1 point.2) := by
  simp only [bayesianGame_payoff]
  exact (((measurable_pi_apply i).comp measurable_snd).mul
      ((A.outcome_measurable i).comp measurable_fst)).sub
      ((payments i).comp measurable_fst)

/-- Integrable realized utility on the original state space gives an admissible
incumbent under the joint type law. -/
theorem incumbentPayoffsIntegrable_bidStrategy
    (β : ℝ → ℝ) (measurable : Measurable β)
    (payments : ∀ i, Measurable (A.rules.payment i))
    (incumbent : ∀ i, Integrable (fun sample =>
      (valuationEnvironment n).utility A.rules i (A.θ · sample)
        (fun j => β (A.θ j sample))) ℙ) :
    A.bayesianGame.IncumbentPayoffsIntegrable A.typeLaw (A.bidStrategy β measurable) := by
  intro i
  have payoffMeasurable := A.bayesianGame.measurable_payoff_comp
    (A.measurable_bayesianGame_payoff payments) i (A.bidStrategy β measurable)
  change Integrable _ (Measure.map (fun sample i => A.θ i sample) ℙ)
  apply (integrable_map_measure payoffMeasurable.aestronglyMeasurable
    (Measurable.of_eval A.θ_measurable).aemeasurable).mpr
  exact incumbent i

/-- Conditional beliefs under independence recover the native interim quantities for each bid. -/
theorem interimPayoffAction_bidStrategy [A.IsIPV]
    (allocation : IsUnitIntervalAllocation A.rules (fun outcome i => outcome i))
    (β : ℝ → ℝ) (measurable : Measurable β)
    (payments : ∀ i, Measurable (A.rules.payment i))
    (integrable_payments : ∀ i bid,
      Integrable (fun sample => A.rules.payment i
        (Function.update (fun j => β (A.θ j sample)) i bid)) ℙ)
    (i : Fin n) (value bid : ℝ) :
    A.bayesianGame.interimPayoffAction A.typeLaw A.independentBeliefs i value bid
        (A.bidStrategy β measurable) =
      value * A.q_strat β i bid - A.p_strat β i bid := by
  have opponentMeasurable : Measurable (fun sample => drop i (A.θ · sample)) :=
    (measurable_drop i).comp (Measurable.of_eval A.θ_measurable)
  have conditionalMeasurable : Measurable (fun opponents =>
      A.bayesianGame.interimPayoffActionIntegrand i value bid
        (A.bidStrategy β measurable) opponents) :=
    (A.bayesianGame.measurable_interimPayoffActionIntegrand
      (A.measurable_bayesianGame_payoff payments) i (A.bidStrategy β measurable)).comp
        ((measurable_const (a := (value, bid))).prodMk measurable_id)
  have actual (sample : Ω) :
      A.bayesianGame.interimPayoffActionIntegrand i value bid (A.bidStrategy β measurable)
          (drop i (A.θ · sample)) =
        value * A.rules.outcome (Function.update (fun j => β (A.θ j sample)) i bid) i -
          A.rules.payment i (Function.update (fun j => β (A.θ j sample)) i bid) := by
    change A.bayesianGame.payoff i
      (Function.update (fun j => β (insert i value (drop i (A.θ · sample)) j)) i bid)
      (insert i value (drop i (A.θ · sample))) = _
    have sameBids :
        Function.update (fun j => β (insert i value (drop i (A.θ · sample)) j)) i bid =
          Function.update (fun j => β (A.θ j sample)) i bid := by
      funext j
      by_cases equal : j = i
      · subst j
        simp
      · simp [Function.update_of_ne equal, insert_of_ne _ _ _ equal, drop]
    rw [bayesianGame_payoff, insert_self, sameBids]
  unfold BayesianGame.interimPayoffAction
  rw [A.independentBeliefs_opponents,
    integral_map opponentMeasurable.aemeasurable conditionalMeasurable.aestronglyMeasurable]
  simp_rw [actual]
  rw [integral_sub ((A.integrable_allocation_strat allocation measurable i bid).const_mul value)
    (integrable_payments i bid), integral_const_mul]
  rfl

/-- Declared type intervals contain the own-type marginal almost surely. -/
theorem marginalType_interval_compl [HasBoundedTypes A] (i : Fin n) :
    marginalType A.typeLaw i (A.interval i)ᶜ = 0 := by
  have marginal : marginalType A.typeLaw i = Measure.map (A.θ i) ℙ := by
    unfold marginalType typeLaw
    rw [Measure.map_map (measurable_pi_apply i) (Measurable.of_eval A.θ_measurable)]
    rfl
  rw [marginal, Measure.map_apply (A.θ_measurable i) measurableSet_Icc.compl]
  have empty : (A.θ i) ⁻¹' (A.interval i)ᶜ = ∅ := by
    ext sample
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact HasBoundedTypes.θ_in (A := A) i sample
  rw [empty, measure_empty]

/-- Original-bid interim IC on the supported type intervals gives native Bayesian equilibrium. -/
theorem isBNE_of_universalIC [A.IsIPV] [HasBoundedTypes A]
    (allocation : IsUnitIntervalAllocation A.rules (fun outcome i => outcome i))
    (β : ℝ → ℝ) (measurable : Measurable β)
    (payments : ∀ i, Measurable (A.rules.payment i))
    (integrable_payments : ∀ i bid,
      Integrable (fun sample => A.rules.payment i
        (Function.update (fun j => β (A.θ j sample)) i bid)) ℙ)
    (incumbent : A.bayesianGame.IncumbentPayoffsIntegrable A.typeLaw
      (A.bidStrategy β measurable))
    (incentives : ∀ i, BidderProblem.HasUniversalIC (A.toBidderProblem allocation β i) univ) :
    A.bayesianGame.IsBNE A.typeLaw (A.bidStrategy β measurable) := by
  apply A.bayesianGame.isBNE_of_best_response_on_ae_set A.typeLaw A.independentBeliefs
    (A.measurable_bayesianGame_payoff payments) (A.bidStrategy β measurable) incumbent A.interval
    (A.marginalType_interval_compl)
  intro i value member bid
  change A.bayesianGame.interimPayoffAction A.typeLaw A.independentBeliefs i value bid
      (A.bidStrategy β measurable) ≤
    A.bayesianGame.interimPayoffAction A.typeLaw A.independentBeliefs i value (β value)
      (A.bidStrategy β measurable)
  rw [A.interimPayoffAction_bidStrategy allocation β measurable payments integrable_payments,
    A.interimPayoffAction_bidStrategy allocation β measurable payments integrable_payments]
  exact (incentives i).universalIC value member bid (mem_univ _)

end Auction

end

end MathEconLib
