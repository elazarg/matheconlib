/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.ConditionalIncentiveControls

/-!
# Conditional incentives under correlated binary types

Each own-type marginal has two positive atoms although mixed joint profiles
have zero probability. Conditional beliefs reveal the opponent's true type.
Truthful reporting is optimal and the native ex-ante and atomic-interim APIs
apply without independence or full support of the joint prior.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.ConditionalIncentiveCorrelated

open Set MeasureTheory ProbabilityTheory
open MathEconLib.Mechanism MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior
open MathEconLibTest.ConditionalBeliefs
open DirectMechanism.Quasilinear
open scoped ENNReal

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

abbrev mechanism := ConditionalIncentiveControls.mechanism

def environment : QuasilinearEnvironment Bool (fun _ => Bool) (Bool → Bool) where
  value player types outcome := if player then 0 else
    if outcome false = types true then 1 else 0

abbrev game := mechanism.inducedBayesianGame environment

theorem interim_formula (player type report : Bool) :
    interimUtility environment mechanism correlatedPrior correlatedBeliefs player type report =
      if player then 0 else if report = type then 1 else 0 := by
  cases player <;> cases type <;> cases report <;>
    simp [interimUtility, BayesianGame.interimPayoffAction,
      BayesianGame.interimPayoffActionIntegrand,
      QuasilinearEnvironment.utility,
      MathEconLib.Mechanism.inducedBayesianGame, environment, mechanism,
      ConditionalIncentiveControls.mechanism, correlatedBeliefs, opponents,
      Kernel.deterministic_apply]

theorem truthful_isBIC : IsBIC environment mechanism correlatedPrior correlatedBeliefs := by
  constructor
  · intro player type _ report _
    exact Integrable.of_finite
  · intro player type _ report _
    rw [interim_formula, interim_formula]
    cases player <;> cases type <;> cases report <;> norm_num

theorem measurable_game_payoff (player : Bool) :
    Measurable (fun point : (Bool → Bool) × (Bool → Bool) =>
      game.payoff player point.1 point.2) := measurable_of_countable _

theorem truthful_isBNE :
    game.IsBNE correlatedPrior (truthfulStrategy environment mechanism) :=
  IsBIC.isBNE environment mechanism correlatedPrior correlatedBeliefs truthful_isBIC
    measurable_game_payoff (fun _ => Integrable.of_finite)

theorem marginal_mass (player type : Bool) :
    marginalType correlatedPrior player {type} = (1 / 2 : ℝ≥0∞) := by
  simp only [marginalType, correlatedPrior,
    Measure.map_add _ _ (measurable_pi_apply player),
    Measure.map_smul _ (measurable_pi_apply player).aemeasurable,
    Measure.map_dirac' (measurable_pi_apply player)]
  cases type <;> simp [profile]

/-- Positive marginal masses do not require positive mass at every joint type profile. -/
theorem mixed_profile_null : correlatedPrior {fun player : Bool => player} = 0 := by
  have false_ne : profile false ≠ (fun player : Bool => player) := by
    intro equal
    exact Bool.false_ne_true (congrFun equal true)
  have true_ne : profile true ≠ (fun player : Bool => player) := by
    intro equal
    exact Bool.noConfusion (congrFun equal false)
  simp [correlatedPrior, false_ne, true_ne]

/-- The native atom theorem recovers every interim comparison from the ex-ante verdict. -/
theorem every_type_optimal (player type action : Bool) :
    game.interimPayoffAction correlatedPrior correlatedBeliefs player type action
        (truthfulStrategy environment mechanism) ≤
      game.interimPayoff correlatedPrior correlatedBeliefs player type
        (truthfulStrategy environment mechanism) := by
  exact truthful_isBNE.interim_bestResponse_of_nonzero_atom (B := correlatedBeliefs)
    measurable_game_payoff
    (fun _ => Filter.Eventually.of_forall fun _ _ => Integrable.of_finite)
    player type (by rw [marginal_mass]; norm_num) action

end MathEconLibTest.AbstractionExperiments.ConditionalIncentiveCorrelated
