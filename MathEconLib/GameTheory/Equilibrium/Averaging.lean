/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Simulation
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Equilibrium transport by averaging source deviations

An admitted target deviation may be bounded by an integral of admissible source
deviation values. Ordered integration transports optimality even for vector
values. For real values a supported admissible source state bounds the mean,
giving a reusable `GameSimulation`. No finiteness of the state space is required.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory

universe u v w x r

namespace EquilibriumProblem

variable {S : Type u} {I : Type v} {T : Type w} {J : Type x} {V : Type r}
    [MeasurableSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}

/-- Averaging admissible deviations transports optimality for ordered vector
values. The represented target value may be smaller than its source mean. -/
theorem IsDeviationOptimal.of_integral_bounds {s : S} {t : T}
    (h : P.IsDeviationOptimal s) (g : J → I)
    (hbase : ∀ j, P.value (g j) s ≤ Q.value j t)
    (hmix : ∀ j t', Q.deviation j t t' →
      ∃ μ : ProbabilityMeasure S, Integrable (P.value (g j)) μ ∧
        (∀ᵐ s' ∂(μ : Measure S), P.deviation (g j) s s') ∧
        Q.value j t' ≤ ∫ s', P.value (g j) s' ∂(μ : Measure S)) : Q.IsDeviationOptimal t := by
  intro j t' ht'
  obtain ⟨μ, hint, hdev, hbound⟩ := hmix j t' ht'
  have hle : ∀ᵐ s' ∂(μ : Measure S), P.value (g j) s' ≤ P.value (g j) s :=
    hdev.mono fun s' hs' ↦ h (g j) s' hs'
  have havg : (∫ s', P.value (g j) s' ∂(μ : Measure S)) ≤ P.value (g j) s := by
    simpa using integral_mono_ae hint (integrable_const (P.value (g j) s)) hle
  exact hbound.trans (havg.trans (hbase j))

/-- Full equilibrium transport also checks validity of the target incumbent. -/
theorem IsEquilibrium.of_integral_bounds {s : S} {t : T}
    (h : P.IsEquilibrium s) (g : J → I) (hvalid : Q.valid t)
    (hbase : ∀ j, P.value (g j) s ≤ Q.value j t)
    (hmix : ∀ j t', Q.deviation j t t' →
      ∃ μ : ProbabilityMeasure S, Integrable (P.value (g j)) μ ∧
        (∀ᵐ s' ∂(μ : Measure S), P.deviation (g j) s s') ∧
        Q.value j t' ≤ ∫ s', P.value (g j) s' ∂(μ : Measure S)) : Q.IsEquilibrium t :=
  ⟨hvalid, h.deviation_le.of_integral_bounds g hbase hmix⟩

end EquilibriumProblem

namespace GameSimulation

variable {S : Type u} {I : Type v} {T : Type w} {J : Type x} [MeasurableSpace S]
    {P : EquilibriumProblem S I ℝ} {Q : EquilibriumProblem T J ℝ}

/-- Integrable scalar mixture bounds yield one admissible dominating witness.
The null-set exclusion ensures that the witness is a legal deviation. -/
def ofIntegralBounds (f : S → T) (g : J → I)
    (hbase : ∀ j s, P.value (g j) s ≤ Q.value j (f s))
    (hvalid : ∀ s, P.valid s → Q.valid (f s))
    (hmix : ∀ j s t, Q.deviation j (f s) t →
      ∃ μ : ProbabilityMeasure S, Integrable (P.value (g j)) μ ∧
        (∀ᵐ s' ∂(μ : Measure S), P.deviation (g j) s s') ∧
        Q.value j t ≤ ∫ s', P.value (g j) s' ∂(μ : Measure S)) : GameSimulation P Q where
  toFun := f
  deviatorMap := g
  valueMap _ := OrderHom.id
  value_le := hbase
  valid_preserves := hvalid
  deviation_dominated j s t ht := by
    obtain ⟨μ, hint, hdev, hbound⟩ := hmix j s t ht
    obtain ⟨s', hs', hmean⟩ := exists_notMem_null_integral_le hint (ae_iff.mp hdev)
    exact ⟨s', by simpa using hs', hbound.trans hmean⟩

end GameSimulation

end MathEconLib.GameTheory
