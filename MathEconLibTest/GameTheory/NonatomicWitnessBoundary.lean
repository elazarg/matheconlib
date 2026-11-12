/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Outcome
public import MathEconLibExamples.AllPurchase.UniformProbability

/-!
# Successful nonatomic mixtures need not retain a positive-mass action

A constant successful stochastic outcome game is flattened by the native
probability-measure map and join operations. Its action law is a nonatomic
uniform value law. The flattened event is certain, but no action singleton has
positive mass. This distinguishes positive-atom witness provenance from success
of a general measurable mixture; it makes no assertion about topological support
or about other witness relations.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.NonatomicWitnessBoundary

open MathEconLib.GameTheory MeasureTheory ProbabilityTheory
open MathEconLib.Examples.AllPurchase.UniformProbability
open scoped ENNReal

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

/-- The actual pushforward law of one coordinate of the uniform example. -/
def actionLaw : ProbabilityMeasure ℝ :=
  ⟨Measure.map (value 0) (ℙ : Measure Ω), inferInstance⟩

instance : NullSingletonClass (actionLaw : Measure ℝ) := noAtoms_value 0

theorem action_singleton_zero (action : ℝ) :
    (actionLaw : Measure ℝ) {action} = 0 := measure_singleton action

/-- A pure successful stochastic outcome, viewed as a probability measure. -/
def pureSuccess : ProbabilityMeasure Bool := ⟨Measure.dirac true, inferInstance⟩

def game : OutcomeGame Unit (fun _ => ℝ) (ProbabilityMeasure Bool) where
  outcome _ := pureSuccess

instance : game.Measurable := ⟨measurable_const⟩

def profile : Unit → ProbabilityMeasure ℝ := fun _ => actionLaw

/-- Native independent mixing maps the profile law to a Dirac law on outcome laws. -/
theorem mixed_eq_dirac :
    (game.mixed.outcome profile : Measure (ProbabilityMeasure Bool)) =
      Measure.dirac pureSuccess := by
  change (Measure.pi (fun _ : Unit => (actionLaw : Measure ℝ))).map
    (fun _ => pureSuccess) = _
  rw [Measure.map_const, measure_univ, one_smul]

/-- The actual native flattened law is successful; no replacement flattening is defined. -/
theorem flattened_eq : game.mixedFlattened.outcome profile = pureSuccess := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((game.mixed.outcome profile : Measure (ProbabilityMeasure Bool)).map
    (fun law : ProbabilityMeasure Bool => (law : Measure Bool))).join =
      (pureSuccess : Measure Bool)
  rw [mixed_eq_dirac, Measure.map_dirac' ProbabilityMeasure.measurable_toMeasure,
    Measure.join_dirac]

theorem flattened_success :
    (game.mixedFlattened.outcome profile : Measure Bool) {true} = 1 := by
  rw [flattened_eq]
  simp [pureSuccess]

/-- Every conditional outcome succeeds, despite the absence of action atoms. -/
theorem every_action_success (action : ℝ) :
    (game.outcome (fun _ => action) : Measure Bool) {true} = 1 := by
  simp [game, pureSuccess]

/-- A positive singleton-mass action cannot witness this successful measurable mixture. -/
theorem no_positive_atom_witness :
    ¬ ∃ action : ℝ, 0 < (actionLaw : Measure ℝ) {action} ∧
      0 < (game.outcome (fun _ => action) : Measure Bool) {true} := by
  rintro ⟨action, positive, _⟩
  rw [action_singleton_zero] at positive
  exact (lt_irrefl (0 : ℝ≥0∞)) positive

theorem success_without_positive_atom :
    0 < (game.mixedFlattened.outcome profile : Measure Bool) {true} ∧
      ¬ ∃ action : ℝ, 0 < (actionLaw : Measure ℝ) {action} ∧
        0 < (game.outcome (fun _ => action) : Measure Bool) {true} := by
  constructor
  · rw [flattened_success]
    exact zero_lt_one
  · exact no_positive_atom_witness

end MathEconLibTest.AbstractionExperiments.NonatomicWitnessBoundary
