/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Outcome
public import MathEconLib.Probability.FinDist.Simplex
public import MathEconLib.Probability.FinDist.Support
public import MathEconLib.Probability.FinDist.Expect
public import MathEconLib.ForMathlib.WitnessLift
public import Mathlib.Tactic.NormNum

/-!
# Possibility preferences over finite outcome laws

An event is possible when an outcome in it has positive probability. Comparing
laws by preservation of this possibility is a total preorder. Native finite
mixtures retain a successful supported component, so pure deviations suffice.
Fully supported independent profiles exhaust all possible events in a finite
outcome game. These are explicit law comparisons, separate from expected-payoff
Nash equilibrium. Three binary lotteries rule out an expected-utility model of
the observed comparisons; the relation still has an elementary Boolean score.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.PossibilityLawPreference

open MathEconLib MathEconLib.Probability MathEconLib.GameTheory
open scoped BigOperators

variable {O A : Type*} [Fintype O] [Fintype A]

/-- The specified good event contains an outcome with positive mass. -/
def Possible (good : O → Prop) (law : FinDist O) : Prop :=
  ∃ outcome, 0 < law outcome ∧ good outcome

/-- The good event remains possible whenever it was possible under the first law. -/
def possibilityLE (good : O → Prop) (alternative chosen : FinDist O) : Prop :=
  Possible good alternative → Possible good chosen

theorem possibility_refl (good : O → Prop) (law : FinDist O) :
    possibilityLE good law law := fun success => success

theorem possibility_trans (good : O → Prop) {first second third : FinDist O}
    (left : possibilityLE good first second) (right : possibilityLE good second third) :
    possibilityLE good first third := fun success => right (left success)

theorem possibility_total (good : O → Prop) (first second : FinDist O) :
    possibilityLE good first second ∨ possibilityLE good second first := by
  classical
  by_cases success : Possible good first
  · exact Or.inr (fun _ => success)
  · exact Or.inl (fun impossible => (success impossible).elim)

theorem possible_finMixture_iff (good : O → Prop) (weights : FinDist A)
    (continuation : A → FinDist O) :
    Possible good (FinDist.finMixture weights continuation) ↔
      ∃ action, 0 < weights action ∧ Possible good (continuation action) := by
  constructor
  · rintro ⟨outcome, positive, success⟩
    obtain ⟨action, supported, conditional⟩ :=
      (FinDist.finMixture_pos_iff weights continuation outcome).mp positive
    exact ⟨action, supported, outcome, conditional, success⟩
  · rintro ⟨action, supported, outcome, conditional, success⟩
    exact ⟨outcome, (FinDist.finMixture_pos_iff weights continuation outcome).mpr
      ⟨action, supported, conditional⟩, success⟩

/-- Every randomized deviation is rejected iff every pure continuation is rejected. -/
theorem pure_deviations_suffice (good : O → Prop)
    (continuation : A → FinDist O) (incumbent : FinDist O) :
    (∀ weights : FinDist A,
      possibilityLE good (FinDist.finMixture weights continuation) incumbent) ↔
      ∀ action, possibilityLE good (continuation action) incumbent := by
  classical
  constructor
  · intro all action
    simpa only [FinDist.finMixture_pure] using all (FinDist.pure action)
  · intro pure weights success
    obtain ⟨action, _, conditional⟩ :=
      (possible_finMixture_iff good weights continuation).mp success
    exact pure action conditional

/-- A failed mixed comparison yields a pure failure with positive original action mass. -/
theorem bad_mixture_has_supported_pure (good : O → Prop)
    (continuation : A → FinDist O) (incumbent : FinDist O) (weights : FinDist A)
    (bad : ¬ possibilityLE good (FinDist.finMixture weights continuation) incumbent) :
    ∃ action, 0 < weights action ∧ ¬ possibilityLE good (continuation action) incumbent := by
  classical
  change ¬ (Possible good (FinDist.finMixture weights continuation) →
    Possible good incumbent) at bad
  obtain ⟨success, failure⟩ := not_imp.mp bad
  obtain ⟨action, supported, conditional⟩ :=
    (possible_finMixture_iff good weights continuation).mp success
  exact ⟨action, supported, fun comparison => failure (comparison conditional)⟩

/-- Witness provenance preserves the supported action behind a bad mixture. -/
def possibilityWitnessLift (good : O → Prop) (continuation : A → FinDist O) :
    WitnessLift
      (fun incumbent action => ¬ possibilityLE good (continuation action) incumbent)
      (fun incumbent weights =>
        ¬ possibilityLE good (FinDist.finMixture weights continuation) incumbent) where
  state := id
  related _ weights action := 0 < weights action
  covers incumbent weights := bad_mixture_has_supported_pure good continuation incumbent weights

/-- A native comparison problem for randomized responses against fixed stochastic continuations. -/
def responseProblem (continuation : A → FinDist O) :
    EquilibriumProblem (FinDist A) Unit (FinDist O) where
  deviation _ _ _ := True
  value _ weights := FinDist.finMixture weights continuation
  valid _ := True

theorem response_equilibrium_iff_pure (good : O → Prop)
    (continuation : A → FinDist O) (weights : FinDist A) :
    (responseProblem continuation).IsEquilibriumWith (fun _ => possibilityLE good) weights ↔
      ∀ action, possibilityLE good (continuation action)
        (FinDist.finMixture weights continuation) := by
  constructor
  · intro equilibrium
    apply (pure_deviations_suffice good continuation _).mp
    intro alternative
    exact equilibrium.deviation_le () alternative trivial
  · intro pure
    refine ⟨trivial, ?_⟩
    intro _ alternative _
    exact (pure_deviations_suffice good continuation _).mpr pure alternative

section IndependentProfiles

variable {I : Type*} [Fintype I] [DecidableEq I] {Action : I → Type*}
  [∀ i, Fintype (Action i)]

/-- Native independent profile sampling followed by the game's native finite stochastic outcome. -/
def outcomeLaw (game : OutcomeGame I Action (FinDist O))
    (profile : ∀ i, FinDist (Action i)) : FinDist O :=
  FinDist.finMixture (FinDist.productD profile) game.outcome

/-- Law-valued rewards use the given comparison, with ordinary unilateral replacements. -/
def lawProblem (game : OutcomeGame I Action (FinDist O)) :
    EquilibriumProblem (∀ i, FinDist (Action i)) I (FinDist O) where
  deviation player profile alternative :=
    ∃ replacement, alternative = Function.update profile player replacement
  value _ profile := outcomeLaw game profile
  valid _ := True

/-- Full support admits every event achievable by any pure outcome continuation,
so no unilateral randomized replacement can improve its possibility score. -/
theorem full_support_equilibrium (game : OutcomeGame I Action (FinDist O))
    (good : I → O → Prop) (profile : ∀ i, FinDist (Action i))
    (full : ∀ player action, 0 < profile player action) :
    (lawProblem game).IsEquilibriumWith (fun player => possibilityLE (good player)) profile := by
  refine ⟨trivial, ?_⟩
  intro player alternative _admissible success
  obtain ⟨actions, _, conditional⟩ :=
    (possible_finMixture_iff (good player) (FinDist.productD alternative) game.outcome).mp success
  apply (possible_finMixture_iff (good player) (FinDist.productD profile) game.outcome).mpr
  refine ⟨actions, ?_, conditional⟩
  change 0 < ∏ player, profile player (actions player)
  exact Finset.prod_pos (fun player _ => full player (actions player))

/-- A uniform law-preference equilibrium exists when every finite action type is nonempty. -/
theorem uniform_equilibrium [∀ i, Nonempty (Action i)]
    (game : OutcomeGame I Action (FinDist O)) (good : I → O → Prop) :
    (lawProblem game).IsEquilibriumWith (fun player => possibilityLE (good player))
      (fun _ => FinDist.uniform) := by
  apply full_support_equilibrium
  intro player action
  rw [FinDist.uniform_apply]
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

end IndependentProfiles

section BinaryLotteries

def fair : FinDist Bool :=
  FinDist.mixture ⟨1 / 2, by norm_num, by norm_num⟩
    (FinDist.pure true) (FinDist.pure false)

def lotteries : Fin 3 → FinDist Bool
  | 0 => FinDist.pure false
  | 1 => FinDist.pure true
  | _ => fair

def good : Bool → Prop := fun outcome => outcome = true

theorem pure_true_possible : Possible good (FinDist.pure true) :=
  ⟨true, by simp, rfl⟩

theorem pure_false_impossible : ¬ Possible good (FinDist.pure false) := by
  rintro ⟨outcome, positive, success⟩
  change outcome = true at success
  subst outcome
  norm_num [FinDist.pure_apply] at positive

theorem fair_possible : Possible good fair := by
  refine ⟨true, ?_, rfl⟩
  change 0 < fair.pmf true
  simp only [fair, FinDist.mixture_pmf, FinDist.pure_pmf]
  norm_num

/-- No expected utility over Bool reproduces even the comparisons among these three lotteries. -/
theorem lotteries_not_expected_utility :
    ¬ ∃ utility : Bool → ℝ, ∀ first second : Fin 3,
      possibilityLE good (lotteries first) (lotteries second) ↔
        (lotteries first).expect utility ≤ (lotteries second).expect utility := by
  rintro ⟨utility, represents⟩
  have true_le_fair := (represents 1 2).mp (fun _ => fair_possible)
  change (FinDist.pure true).expect utility ≤ fair.expect utility at true_le_fair
  rw [FinDist.expect_pure] at true_le_fair
  simp only [fair, FinDist.expect_mixture, FinDist.expect_pure] at true_le_fair
  have pure_bound : utility true ≤ utility false := by
    norm_num only [smul_eq_mul] at true_le_fair
    linarith
  have false_comparison := (represents 1 0).mpr
    (by simpa only [lotteries, FinDist.expect_pure] using pure_bound)
  exact pure_false_impossible (false_comparison pure_true_possible)

def lotteryGame : OutcomeGame Unit (fun _ => Fin 3) (FinDist Bool) where
  outcome actions := lotteries (actions ())

/-- The same native game offers pure failure, pure success, and a genuine random lottery. -/
theorem lotteryGame_uniform_equilibrium :
    (lawProblem lotteryGame).IsEquilibriumWith (fun _ => possibilityLE good)
      (fun _ => FinDist.uniform) :=
  uniform_equilibrium lotteryGame (fun _ => good)

end BinaryLotteries

end MathEconLibTest.AbstractionExperiments.PossibilityLawPreference
