/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.PossibilityLawPreference

/-!
# Positive type mass does not recover conditional possibility optimality

At the false type success is automatic; at the true type the action determines
success. Ex-ante possibility already holds under the constant-false strategy,
so every randomized contingent deviation is rejected. Nevertheless, the true
type has positive prior probability and a strict conditional improvement.
This concerns explicit possibility comparisons, not expected-utility incentives.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.PossibilityInformationBoundary

open MathEconLib.Probability MathEconLib.GameTheory
open PossibilityLawPreference

abbrev ContingentStrategy := Bool → Bool

def prior : FinDist Bool := fair

theorem prior_atom_mass (type : Bool) : prior type = 1 / 2 := by
  change prior.pmf type = 1 / 2
  simp only [prior, fair, FinDist.mixture_pmf, FinDist.pure_pmf]
  cases type <;> norm_num

def conditionalLaw (strategy : ContingentStrategy) (type : Bool) : FinDist Bool :=
  FinDist.pure (if type then strategy type else true)

def exAnteLaw (strategy : ContingentStrategy) : FinDist Bool :=
  FinDist.finMixture prior (conditionalLaw strategy)

def incumbent : ContingentStrategy := fun _ => false

/-- The positive-mass false type makes success possible ex ante. -/
theorem incumbent_possible : Possible good (exAnteLaw incumbent) := by
  apply (possible_finMixture_iff good prior (conditionalLaw incumbent)).mpr
  refine ⟨false, ?_, true, ?_, rfl⟩
  · rw [prior_atom_mass]
    norm_num
  · change 0 < (FinDist.pure true) true
    simp

/-- Every distribution over contingent strategies is admitted as a deviation. -/
theorem exAnte_equilibrium :
    (responseProblem exAnteLaw).IsEquilibriumWith (fun _ => possibilityLE good)
      (FinDist.pure incumbent) := by
  apply (response_equilibrium_iff_pure good exAnteLaw (FinDist.pure incumbent)).mpr
  intro strategy _
  simpa only [FinDist.finMixture_pure] using incumbent_possible

/-- At the positive-mass true type, reporting true creates a previously impossible success. -/
theorem conditional_improvement :
    0 < prior true ∧
      possibilityLE good (conditionalLaw incumbent true) (conditionalLaw (fun _ => true) true) ∧
      ¬ possibilityLE good (conditionalLaw (fun _ => true) true)
        (conditionalLaw incumbent true) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [prior_atom_mass]
    norm_num
  · intro _
    exact pure_true_possible
  · change ¬ possibilityLE good (FinDist.pure true) (FinDist.pure false)
    exact fun comparison => pure_false_impossible (comparison pure_true_possible)

end MathEconLibTest.AbstractionExperiments.PossibilityInformationBoundary
