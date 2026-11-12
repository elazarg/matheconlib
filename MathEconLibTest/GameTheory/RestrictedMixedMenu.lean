/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.PossibilityLawPreference

/-!
# Admissible pure witnesses under restricted mixed menus

A mean quantity budget admits a fair lottery over quantities zero and two,
but excludes the pure quantity-two action. Pure admissible deviations therefore
miss a genuine possibility improvement even though the incumbent is valid and
the pure menu is nonempty. Support-hereditary admissibility repairs the witness
argument: an extracted supported action must itself remain admissible.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.RestrictedMixedMenu

open MathEconLib MathEconLib.Probability MathEconLib.GameTheory
open PossibilityLawPreference

def quantity (action : Bool) : ℝ := if action then 2 else 0

def admitted (law : FinDist Bool) : Prop := law.expect quantity ≤ 1

abbrev incumbent : FinDist Bool := FinDist.pure false

/-- The same mean budget guards candidates and each admitted deviation. -/
def budgetResponse : EquilibriumProblem (FinDist Bool) Unit (FinDist Bool) where
  deviation _ _ alternative := admitted alternative
  value _ law := law
  valid := admitted

theorem admitted_pure_iff (action : Bool) : admitted (FinDist.pure action) ↔ action = false := by
  cases action <;> norm_num [admitted, FinDist.expect_pure, quantity]

theorem incumbent_admitted : admitted incumbent := (admitted_pure_iff false).mpr rfl

theorem pure_menu_nonempty : ∃ action : Bool, admitted (FinDist.pure action) :=
  ⟨false, incumbent_admitted⟩

theorem pure_true_excluded : ¬ admitted (FinDist.pure true) := by
  rw [admitted_pure_iff]
  decide

theorem fair_admitted : admitted fair := by
  change fair.expect quantity ≤ 1
  simp only [fair, FinDist.expect_mixture, FinDist.expect_pure, quantity, smul_eq_mul]
  norm_num

theorem all_admitted_pure_rejected :
    ∀ action : Bool, admitted (FinDist.pure action) →
      possibilityLE good (FinDist.pure action) incumbent := by
  intro action allowed
  have equal : action = false := (admitted_pure_iff action).mp allowed
  subst action
  exact possibility_refl good incumbent

theorem fair_improves : ¬ possibilityLE good fair incumbent :=
  fun comparison => pure_false_impossible (comparison fair_possible)

theorem fair_strict_improvement :
    possibilityLE good incumbent fair ∧ ¬ possibilityLE good fair incumbent :=
  ⟨fun _ => fair_possible, fair_improves⟩

/-- The actual valid incumbent fails native equilibrium under an admitted mixed deviation. -/
theorem incumbent_not_equilibrium :
    ¬ budgetResponse.IsEquilibriumWith (fun _ => possibilityLE good) incumbent := by
  intro equilibrium
  exact fair_improves (equilibrium.deviation_le () fair fair_admitted)

/-- The contributing successful pure action is precisely the one the mean budget excludes. -/
theorem mean_budget_not_support_hereditary :
    ¬ ∀ weights : FinDist Bool, admitted weights →
      ∀ action, 0 < weights action → admitted (FinDist.pure action) := by
  intro hereditary
  obtain ⟨outcome, positive, success⟩ := fair_possible
  have equal : outcome = true := success
  subst outcome
  exact pure_true_excluded (hereditary fair fair_admitted true positive)

section SupportHereditary

variable {A O : Type*} [Fintype A] [Fintype O] [DecidableEq A]

/-- A supported pure obstruction remains admissible under support-hereditary menus. -/
def admissiblePossibilityWitnessLift (good : O → Prop) (continuation : A → FinDist O)
    (allowed : FinDist A → Prop)
    (supportHereditary : ∀ weights, allowed weights →
      ∀ action, 0 < weights action → allowed (FinDist.pure action)) :
    WitnessLift
      (fun incumbent action => allowed (FinDist.pure action) ∧
        ¬ possibilityLE good (continuation action) incumbent)
      (fun incumbent weights => allowed weights ∧
        ¬ possibilityLE good (FinDist.finMixture weights continuation) incumbent) where
  state := id
  related _ weights action :=
    allowed weights ∧ 0 < weights action ∧ allowed (FinDist.pure action)
  covers incumbent weights violation := by
    obtain ⟨action, positive, pureViolation⟩ :=
      (possibilityWitnessLift good continuation).covers incumbent weights violation.2
    have pureAllowed := supportHereditary weights violation.1 action positive
    exact ⟨action, ⟨violation.1, positive, pureAllowed⟩, pureAllowed, pureViolation⟩

/-- Support-hereditary menus identify admissible pure and mixed comparisons.
This theorem compares deviations; validity of an incumbent remains a separate guard. -/
theorem pure_deviations_suffice_of_support_hereditary
    (good : O → Prop) (continuation : A → FinDist O) (allowed : FinDist A → Prop)
    (supportHereditary : ∀ weights, allowed weights →
      ∀ action, 0 < weights action → allowed (FinDist.pure action))
    (incumbent : FinDist O) :
    (∀ weights, allowed weights →
      possibilityLE good (FinDist.finMixture weights continuation) incumbent) ↔
      ∀ action, allowed (FinDist.pure action) →
        possibilityLE good (continuation action) incumbent := by
  constructor
  · intro all action permitted
    simpa only [FinDist.finMixture_pure] using all (FinDist.pure action) permitted
  · intro pure weights permitted
    exact Classical.byContradiction fun violation =>
      (admissiblePossibilityWitnessLift good continuation allowed supportHereditary).transport
        (c := incumbent) (fun action bad => bad.2 (pure action bad.1))
        weights ⟨permitted, violation⟩

end SupportHereditary

/-- The ex-post budget is intentionally stronger than the preceding mean budget:
every supported quantity must satisfy the bound individually. -/
def exPostAllowed (law : FinDist Bool) : Prop :=
  ∀ action, 0 < law action → quantity action ≤ 1

theorem exPost_support_hereditary :
    ∀ weights, exPostAllowed weights →
      ∀ action, 0 < weights action → exPostAllowed (FinDist.pure action) := by
  intro weights allowed action positive other supported
  have ownBudget := allowed action positive
  by_cases equal : action = other
  · simpa only [← equal] using ownBudget
  · simp only [FinDist.pure_apply, ite_eq_right equal] at supported
    exact (lt_irrefl _ supported).elim

theorem exPost_incumbent_admitted : exPostAllowed incumbent := by
  intro action positive
  cases action <;> norm_num [quantity, FinDist.pure_apply] at *

theorem fair_exPost_excluded : ¬ exPostAllowed fair := by
  intro allowed
  obtain ⟨outcome, positive, success⟩ := fair_possible
  have equal : outcome = true := success
  have budget := allowed outcome positive
  rw [equal] at budget
  norm_num [quantity] at budget

/-- Native deterministic continuations retain the selected action's outcome. -/
def exPostResponse : EquilibriumProblem (FinDist Bool) Unit (FinDist Bool) where
  deviation _ _ alternative := exPostAllowed alternative
  value _ weights := weights
  valid := exPostAllowed

/-- The repaired theorem certifies the valid incumbent for the stronger budget. -/
theorem exPost_incumbent_equilibrium :
    exPostResponse.IsEquilibriumWith (fun _ => possibilityLE good) incumbent := by
  refine ⟨exPost_incumbent_admitted, ?_⟩
  have comparisons :=
    (pure_deviations_suffice_of_support_hereditary good FinDist.pure exPostAllowed
      exPost_support_hereditary incumbent).mpr (by
        intro action allowed
        cases action
        · exact possibility_refl good incumbent
        · have impossible := allowed true (by simp)
          norm_num [quantity] at impossible)
  intro _ alternative permitted
  change possibilityLE good alternative incumbent
  simpa only [FinDist.finMixture_pure_right] using comparisons alternative permitted

end MathEconLibTest.AbstractionExperiments.RestrictedMixedMenu
