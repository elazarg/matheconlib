/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Outcome
public import MathEconLib.ForMathlib.WitnessLift
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Tactic.NormNum

/-!
# Possibility comparisons under arbitrary discrete mixtures

Mathlib's bind support identity supplies an actual supported pure action behind
any possible event in a randomized outcome. Pure-deviation sufficiency and a
witness lift require no finite action or outcome carrier. A genuine geometric
incumbent has infinite support and is optimal under a possibility comparison in
a native law-valued response problem. These comparisons make no expected-utility
or integrability claim and introduce no additional probability carrier.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.CountablePossibility

open MathEconLib MathEconLib.GameTheory MeasureTheory ProbabilityTheory Set

variable {Action Outcome : Type*}

def Possible (good : Outcome → Prop) (law : PMF Outcome) : Prop :=
  ∃ outcome ∈ law.support, good outcome

/-- The chosen law retains possibility of the specified event. -/
def possibilityLE (good : Outcome → Prop) (alternative chosen : PMF Outcome) : Prop :=
  Possible good alternative → Possible good chosen

/-- No finiteness assumption is needed: every successful bind has a supported component. -/
theorem possible_bind_iff (good : Outcome → Prop) (weights : PMF Action)
    (continuation : Action → PMF Outcome) :
    Possible good (weights.bind continuation) ↔
      ∃ action ∈ weights.support, Possible good (continuation action) := by
  constructor
  · rintro ⟨outcome, supported, success⟩
    obtain ⟨action, supportedAction, supportedOutcome⟩ :=
      (PMF.mem_support_bind_iff weights continuation outcome).mp supported
    exact ⟨action, supportedAction, outcome, supportedOutcome, success⟩
  · rintro ⟨action, supportedAction, outcome, supportedOutcome, success⟩
    exact ⟨outcome, (PMF.mem_support_bind_iff weights continuation outcome).mpr
      ⟨action, supportedAction, supportedOutcome⟩, success⟩

/-- Arbitrary discrete randomized deviations suffice exactly when pure deviations suffice. -/
theorem pure_deviations_suffice (good : Outcome → Prop)
    (continuation : Action → PMF Outcome) (incumbent : PMF Outcome) :
    (∀ weights : PMF Action, possibilityLE good (weights.bind continuation) incumbent) ↔
      ∀ action, possibilityLE good (continuation action) incumbent := by
  constructor
  · intro all action
    simpa only [PMF.pure_bind] using all (PMF.pure action)
  · intro pure weights success
    obtain ⟨action, _, component⟩ := (possible_bind_iff good weights continuation).mp success
    exact pure action component

/-- A bad comparison retains the positive-mass action behind that obstruction. -/
theorem bad_bind_has_positive_atom (good : Outcome → Prop)
    (continuation : Action → PMF Outcome) (incumbent : PMF Outcome) (weights : PMF Action)
    (bad : ¬ possibilityLE good (weights.bind continuation) incumbent) :
    ∃ action, 0 < weights action ∧ ¬ possibilityLE good (continuation action) incumbent := by
  classical
  change ¬ (Possible good (weights.bind continuation) → Possible good incumbent) at bad
  obtain ⟨success, failure⟩ := not_imp.mp bad
  obtain ⟨action, supported, component⟩ := (possible_bind_iff good weights continuation).mp success
  have positive : 0 < weights action :=
    pos_iff_ne_zero.mpr ((PMF.mem_support_iff weights action).mp supported)
  exact ⟨action, positive, fun comparison => failure (comparison component)⟩

/-- The public guarded witness-lift operation can retain the atom from a bad discrete mixture. -/
def possibilityWitnessLift (good : Outcome → Prop) (continuation : Action → PMF Outcome) :
    WitnessLift
      (fun incumbent action => ¬ possibilityLE good (continuation action) incumbent)
      (fun incumbent (weights : PMF Action) =>
        ¬ possibilityLE good (weights.bind continuation) incumbent) where
  state := id
  related _ weights action := 0 < weights action
  covers incumbent weights := bad_bind_has_positive_atom good continuation incumbent weights

/-- Successful actions and unsuccessful actions both occur in the outcome rule. -/
def game : OutcomeGame Unit (fun _ => ℕ) (PMF Bool) where
  outcome actions := if actions () % 2 = 0 then PMF.pure true else PMF.pure false

/-- The native discrete response law samples an action and then its stochastic outcome. -/
def outcomeLaw (weights : PMF ℕ) : PMF Bool :=
  weights.bind (fun action => game.outcome (fun _ => action))

def responseProblem : EquilibriumProblem (PMF ℕ) Unit (PMF Bool) where
  deviation _ _ _ := True
  value _ weights := outcomeLaw weights
  valid _ := True

def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Canonical Mathlib conversion of the geometric probability measure to its discrete law. -/
def geometric : PMF ℕ := (geometricMeasure half).toPMF

theorem geometric_mem_support (action : ℕ) : action ∈ geometric.support := by
  rw [PMF.mem_support_iff]
  change geometricMeasure half {action} ≠ 0
  have nonzero : half ≠ 0 := by
    intro equal
    have impossible := congrArg Subtype.val equal
    norm_num [half] at impossible
  have notOne : half ≠ 1 := by
    intro equal
    have impossible := congrArg Subtype.val equal
    norm_num [half] at impossible
  rw [geometricMeasure_singleton nonzero]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (geometricMeasure_pos nonzero notOne action))

theorem geometric_support : geometric.support = univ := by
  ext action
  simp only [mem_univ, iff_true]
  exact geometric_mem_support action

/-- The incumbent is genuinely infinitely supported, rather than a finite test in disguise. -/
theorem geometric_infinite_support : geometric.support.Infinite := by
  rw [geometric_support]
  exact Set.infinite_univ

/-- Even action zero has positive incumbent mass and yields a successful outcome. -/
theorem geometric_success : Possible (fun outcome => outcome = true) (outcomeLaw geometric) := by
  apply (possible_bind_iff _ geometric (fun action => game.outcome (fun _ => action))).mpr
  refine ⟨0, geometric_mem_support 0, true, ?_, rfl⟩
  simp [game]

/-- Pure-deviation reduction certifies this native equilibrium against every PMF deviation. -/
theorem geometric_equilibrium :
    responseProblem.IsEquilibriumWith
      (fun _ => possibilityLE (fun outcome => outcome = true)) geometric := by
  have pure : ∀ action, possibilityLE (fun outcome => outcome = true)
      (game.outcome (fun _ => action)) (outcomeLaw geometric) :=
    fun _ _ => geometric_success
  have all := (pure_deviations_suffice _
    (fun action => game.outcome (fun _ => action)) (outcomeLaw geometric)).mpr pure
  exact ⟨trivial, fun _ alternative _ => all alternative⟩

end MathEconLibTest.AbstractionExperiments.CountablePossibility
