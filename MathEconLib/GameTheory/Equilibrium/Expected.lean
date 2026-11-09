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

Positive affine changes of real outcome utilities preserve and reflect equilibrium for
probability laws. Integrability is preserved, and affine expectation identities are used only
at valid incumbents and admitted deviations, not at states with undefined expectations.
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

/-- Positive affine changes of real outcome utilities preserve and reflect equilibrium.
No global integrability hypothesis is needed: the expected-value problems already check the
incumbent and the deviations being compared. The integral identities need not hold elsewhere. -/
theorem isEquilibrium_ofExpectedValue_affine_iff
    (D : I → S → S → Prop) (L : S → Measure O) [∀ s, IsProbabilityMeasure (L s)]
    (u : I → O → ℝ) (a c : I → ℝ) (ha : ∀ i, 0 < a i) (s : S) :
    (ofExpectedValue D L (fun i o ↦ a i * u i o + c i)).IsEquilibrium s ↔
      (ofExpectedValue D L u).IsEquilibrium s := by
  have hint i t : Integrable (fun o ↦ a i * u i o + c i) (L t) ↔ Integrable (u i) (L t) :=
    integrable_add_const_iff.trans
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (ha i).ne') _)
  have hmean i t (hi : Integrable (u i) (L t)) :
      (∫ o, a i * u i o + c i ∂L t) = a i * (∫ o, u i o ∂L t) + c i := by
    rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul]
    simp
  simp only [isEquilibrium_iff, ofExpectedValue_valid_iff, hint, isDeviationOptimal_iff,
    ofExpectedValue_deviation_iff, ofExpectedValue_value]
  constructor <;> rintro ⟨hvalid, hdev⟩ <;> refine ⟨hvalid, ?_⟩
  all_goals
    intro i t ht
    simpa only [hmean i t ht.2, hmean i s (hvalid i), add_le_add_iff_right,
      mul_le_mul_iff_right₀ (ha i)] using hdev i t ht

end MathEconLib.GameTheory.EquilibriumProblem
