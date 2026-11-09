/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Equilibrium problems evaluated by expected utility

A family of outcome measures and utilities evaluates a supplied deviation relation. Candidates
must have integrable incumbent utilities; a deviation is admitted when its deviator's
utility is integrable. This construction is shared by mixed Nash and stochastic
outcome games. Values lie in a real Banach space. No measurable structure on states
or global measurability of laws or utilities is required.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.EquilibriumProblem

variable {S I O V : Type*} [MeasurableSpace O]
    [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Expected-utility evaluation admits precisely the supplied deviations with
integrable deviator utility, and requires all incumbent utilities to be integrable. -/
def ofExpectedValue [CompleteSpace V] (D : I → S → S → Prop) (L : S → Measure O)
    (u : I → O → V) :
    EquilibriumProblem S I V where
  deviation i s t := D i s t ∧ Integrable (u i) (L t)
  value i s := ∫ o, u i o ∂L s
  valid s := ∀ i, Integrable (u i) (L s)

variable [CompleteSpace V]

/-- Admissibility combines the underlying relation with integrability. -/
@[simp] lemma ofExpectedValue_deviation_iff (D : I → S → S → Prop) (L : S → Measure O)
    (u : I → O → V) (i : I) (s t : S) :
    (ofExpectedValue D L u).deviation i s t ↔ D i s t ∧ Integrable (u i) (L t) := Iff.rfl

/-- Values are the expected utilities under the outcome law. -/
@[simp] lemma ofExpectedValue_value (D : I → S → S → Prop) (L : S → Measure O)
    (u : I → O → V) (i : I) (s : S) :
    (ofExpectedValue D L u).value i s = ∫ o, u i o ∂L s := rfl

/-- A valid incumbent has integrable utility for every deviator. -/
@[simp] lemma ofExpectedValue_valid_iff (D : I → S → S → Prop) (L : S → Measure O)
    (u : I → O → V) (s : S) :
    (ofExpectedValue D L u).valid s ↔ ∀ i, Integrable (u i) (L s) := Iff.rfl

end MathEconLib.GameTheory.EquilibriumProblem
