/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Continuity of atomless cumulative distribution functions

A CDF is right-continuous. Its left jump is the singleton mass, so
vanishing singleton masses also give left continuity.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- An atomless probability law has a continuous cumulative distribution function. -/
theorem continuous_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] : Continuous (cdf μ : ℝ → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro value
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [(cdf μ).rightLim_eq]
  have jump := (cdf μ).measure_singleton value
  rw [ProbabilityTheory.measure_cdf μ, measure_singleton] at jump
  have noJump : cdf μ value ≤ Function.leftLim (cdf μ) value :=
    sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp jump.symm)
  exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) noJump

end ProbabilityTheory
