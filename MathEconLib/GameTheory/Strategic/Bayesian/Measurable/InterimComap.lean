/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Comap
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Interim

/-!
# Conditional payoffs under action translation

Translating the prescribed and deviating actions preserves conditional payoffs
under the same beliefs and true types. The identity needs no equilibrium premise
or change to the prior and follows from equality of the realized integrands.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.BayesianGame

open BayesianPrior

section ActionTranslation

variable {I : Type*} {Θ : I → Type*} {Actions : I → Type*} {Reports : I → Type*}
    {V : Type*} [DecidableEq I] [∀ i, MeasurableSpace (Θ i)]
    [∀ i, MeasurableSpace (Actions i)] [∀ i, MeasurableSpace (Reports i)]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Translating conditional action payoffs preserves the same conditional beliefs and types. -/
theorem interimPayoffAction_comapActions (G : BayesianGame I Θ Actions V)
    (μ : Measure (∀ i, Θ i)) (beliefs : ConditionalBeliefs μ)
    (κ : ∀ i, {f : Reports i → Actions i // Measurable f})
    (strategy : (G.comapActions (fun i => (κ i).1)).Strategy)
    (i : I) (value : Θ i) (action : Reports i) :
    (G.comapActions (fun i => (κ i).1)).interimPayoffAction μ beliefs i value action
        strategy =
      G.interimPayoffAction μ beliefs i value ((κ i).1 action)
        (Strategy.mapActions G κ strategy) := by
  unfold interimPayoffAction
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun opponents => by
    change G.payoff i
        (fun j => (κ j).1 ((Function.update
          (fun j => (strategy j).1 ((insert i value opponents) j)) i action) j))
        (insert i value opponents) =
      G.payoff i (Function.update
        (fun j => (κ j).1 ((strategy j).1 ((insert i value opponents) j)))
        i ((κ i).1 action)) (insert i value opponents)
    congr 1
    funext j
    exact Function.apply_update (fun j => (κ j).1) _ i action j

end ActionTranslation

end MathEconLib.GameTheory.BayesianGame
