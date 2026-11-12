/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.BayesianEquilibrium
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.InterimComap

/-!
# Bayesian equilibrium with restricted original bids

Action inclusion restricts the actual mechanism-induced Bayesian game without
changing its prior, allocation rule, transfers or true types. Interim incentives
on the selected set of real bids imply native Bayesian equilibrium against every
measurable restricted deviation admitted by the native integrability guard.
The proof reuses the original auction interim identity and conditional averaging.
Its fixed-bid payment guard still quantifies over all real bids, including bids
outside the restricted set. A subset needs no additional measurable-set assumption:
its subtype carries the induced measurable space and inclusion is measurable.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MathEconLib.Auction

open MathEconLib.GameTheory MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n : ℕ} (A : Auction Ω n)

/-- The same measurable strategy, taking its bids in the selected action subtype. -/
def restrictedBidStrategy (S : Set ℝ) (β : ℝ → S) (measurable : Measurable β) :
    (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).Strategy :=
  fun _ => ⟨β, measurable⟩

/-- Restricted action inclusion preserves the original interim allocation/payment expression. -/
theorem interimPayoffAction_restrictedBidStrategy [A.IsIPV]
    (allocation : IsUnitIntervalAllocation A.rules (fun outcome i => outcome i))
    (S : Set ℝ) (β : ℝ → S) (measurable : Measurable β)
    (payments : ∀ i, Measurable (A.rules.payment i))
    (integrable_payments : ∀ i bid,
      Integrable (fun sample => A.rules.payment i
        (Function.update (fun j => (β (A.θ j sample) : ℝ)) i bid)) ℙ)
    (i : Fin n) (value : ℝ) (bid : S) :
    (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).interimPayoffAction
        A.typeLaw A.independentBeliefs i value bid (A.restrictedBidStrategy S β measurable) =
      value * A.q_strat (fun v => (β v : ℝ)) i bid -
        A.p_strat (fun v => (β v : ℝ)) i bid := by
  rw [BayesianGame.interimPayoffAction_comapActions A.bayesianGame A.typeLaw
    A.independentBeliefs (fun _ => ⟨(Subtype.val : S → ℝ), measurable_subtype_coe⟩)]
  exact A.interimPayoffAction_bidStrategy allocation (fun v => (β v : ℝ))
    (measurable_subtype_coe.comp measurable) payments integrable_payments i value bid

/-- Supported-type IC on the original feasible bid set implies actual restricted Bayesian Nash
 equilibrium. Incumbent utility is integrable on the original probability space; fixed-bid payment
 integrability is retained for every real bid, as required by the original interim identity. -/
theorem isBNE_restricted_of_universalIC [A.IsIPV] [HasBoundedTypes A]
    (allocation : IsUnitIntervalAllocation A.rules (fun outcome i => outcome i))
    (S : Set ℝ) (β : ℝ → S) (measurable : Measurable β)
    (payments : ∀ i, Measurable (A.rules.payment i))
    (integrable_payments : ∀ i bid,
      Integrable (fun sample => A.rules.payment i
        (Function.update (fun j => (β (A.θ j sample) : ℝ)) i bid)) ℙ)
    (incumbent : ∀ i, Integrable (fun sample =>
      (valuationEnvironment n).utility A.rules i (A.θ · sample)
        (fun j => (β (A.θ j sample) : ℝ))) ℙ)
    (incentives : ∀ i, BidderProblem.HasUniversalIC
      (A.toBidderProblem allocation (fun v => (β v : ℝ)) i) S) :
    (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).IsBNE A.typeLaw
      (A.restrictedBidStrategy S β measurable) := by
  have bidsMeasurable : Measurable (fun bids : Fin n → S => fun j => (bids j : ℝ)) :=
    Measurable.of_eval fun j => measurable_subtype_coe.comp (measurable_pi_apply j)
  have payoffMeasurable (i : Fin n) :
      Measurable (fun point : (Fin n → S) × (Fin n → ℝ) =>
        (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).payoff
          i point.1 point.2) :=
    (A.measurable_bayesianGame_payoff payments i).comp
      ((bidsMeasurable.comp measurable_fst).prodMk measurable_snd)
  have incumbentIntegrable :
      (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).IncumbentPayoffsIntegrable
        A.typeLaw (A.restrictedBidStrategy S β measurable) := by
    exact A.incumbentPayoffsIntegrable_bidStrategy (fun v => (β v : ℝ))
      (measurable_subtype_coe.comp measurable) payments incumbent
  apply BayesianGame.isBNE_of_best_response_on_ae_set
    (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ)))
      A.typeLaw A.independentBeliefs payoffMeasurable
      (A.restrictedBidStrategy S β measurable) incumbentIntegrable A.interval
      A.marginalType_interval_compl
  intro i value member bid
  change
    (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).interimPayoffAction
        A.typeLaw A.independentBeliefs i value bid (A.restrictedBidStrategy S β measurable) ≤
      (A.bayesianGame.comapActions (fun _ => (Subtype.val : S → ℝ))).interimPayoffAction
        A.typeLaw A.independentBeliefs i value (β value)
        (A.restrictedBidStrategy S β measurable)
  rw [A.interimPayoffAction_restrictedBidStrategy allocation S β measurable payments
      integrable_payments,
    A.interimPayoffAction_restrictedBidStrategy allocation S β measurable payments
      integrable_payments]
  exact (incentives i).universalIC value member bid bid.property

end MathEconLib.Auction
