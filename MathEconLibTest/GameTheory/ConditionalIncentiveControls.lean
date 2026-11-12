/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism.Core.BayesianIC
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.InterimAtoms
public import MathEconLibTest.GameTheory.ConditionalBeliefs
public import Mathlib.Tactic.NormNum

/-!
# Conditional incentives at supported and null types

Two valid conditional-belief versions share a prior and an ex-ante truthful
equilibrium. Pointwise truthful incentives hold under one version and fail under
the other at a null type. Values depend on the full true type profile, while the
mechanism keeps its reported outcome and signed transfers fixed across versions.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.ConditionalIncentiveControls

open Set MeasureTheory ProbabilityTheory
open MathEconLib.Mechanism MathEconLib.GameTheory
open MathEconLib.GameTheory.BayesianPrior
open MathEconLibTest.ConditionalBeliefs
open DirectMechanism.Quasilinear

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

/-- At type false the active player wants false. At type true it wants the
opposite of the other player's true type. The other player has zero value. -/
def environment : QuasilinearEnvironment Bool (fun _ => Bool) (Bool → Bool) where
  value player types outcome := if player then 0 else
    if types false then (if outcome false = !(types true) then 1 else 0)
    else (if outcome false then 0 else 1)

def mechanism : DirectMechanism Bool (fun _ => Bool) (Bool → Bool) where
  outcome reports := reports
  transfer _ _ := 0

abbrev game := mechanism.inducedBayesianGame environment

/-- A fixed outcome has different values when only the opponent's true type changes. -/
theorem not_private_values : ¬ environment.IsPrivateValues := by
  intro privateValues
  have equal := congrFun
    (privateValues false (fun _ => true) (fun player => !player) rfl) (fun _ => true)
  norm_num [environment] at equal

theorem constant_interim (player type report : Bool) :
    interimUtility environment mechanism nullPrior constantBeliefs player type report =
      if player then 0 else if type then (if report then 1 else 0)
      else (if report then 0 else 1) := by
  cases player <;> cases type <;> cases report <;>
    simp [interimUtility, BayesianGame.interimPayoffAction,
      BayesianGame.interimPayoffActionIntegrand,
      QuasilinearEnvironment.utility,
      MathEconLib.Mechanism.inducedBayesianGame, environment, mechanism,
      constantBeliefs, opponents, Kernel.const_apply]

theorem matching_interim (player type report : Bool) :
    interimUtility environment mechanism nullPrior matchingBeliefs player type report =
      if player then 0 else if report then 0 else 1 := by
  cases player <;> cases type <;> cases report <;>
    simp [interimUtility, BayesianGame.interimPayoffAction,
      BayesianGame.interimPayoffActionIntegrand,
      QuasilinearEnvironment.utility,
      MathEconLib.Mechanism.inducedBayesianGame, environment, mechanism,
      matchingBeliefs, opponents, Kernel.deterministic_apply]

/-- All original conditional reports are integrable; truth is pointwise optimal. -/
theorem constant_isBIC : IsBIC environment mechanism nullPrior constantBeliefs := by
  constructor
  · intro player type _ report _
    exact Integrable.of_finite
  · intro player type _ report _
    rw [constant_interim, constant_interim]
    cases player <;> cases type <;> cases report <;> norm_num

theorem measurable_game_payoff (player : Bool) :
    Measurable (fun point : (Bool → Bool) × (Bool → Bool) =>
      game.payoff player point.1 point.2) := measurable_of_countable _

/-- Native averaging transports the pointwise conditional comparisons to an ex-ante verdict. -/
theorem truthful_isBNE :
    game.IsBNE nullPrior (truthfulStrategy environment mechanism) :=
  IsBIC.isBNE environment mechanism nullPrior constantBeliefs constant_isBIC
    measurable_game_payoff (fun _ => Integrable.of_finite)

/-- The same prior and ex-ante game admit another valid conditional-belief version
under which a null type profits strictly by lying. -/
theorem matching_not_isBIC : ¬ IsBIC environment mechanism nullPrior matchingBeliefs := by
  intro incentive
  have comparison := incentive.bic false true (mem_univ _) false (mem_univ _)
  rw [matching_interim, matching_interim] at comparison
  norm_num at comparison

theorem null_true_mass : marginalType nullPrior false {true} = 0 := by
  simp [marginalType, nullPrior, profile, Measure.map_dirac' (measurable_pi_apply false)]

/-- The nonnull type still satisfies every interim comparison under the second version. -/
theorem supported_false_optimal (action : Bool) :
    game.interimPayoffAction nullPrior matchingBeliefs false false action
        (truthfulStrategy environment mechanism) ≤
      game.interimPayoff nullPrior matchingBeliefs false false
        (truthfulStrategy environment mechanism) := by
  apply truthful_isBNE.interim_bestResponse_of_nonzero_atom measurable_game_payoff
    (B := matchingBeliefs) (i := false) (type := false)
  · intro player
    exact Filter.Eventually.of_forall fun type action => Integrable.of_finite
  · simp [marginalType, nullPrior, profile, Measure.map_dirac' (measurable_pi_apply false)]

end MathEconLibTest.AbstractionExperiments.ConditionalIncentiveControls
