/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism.Core.SolutionConcepts

/-!
# Explicit welfare weights and changes of utility units

Welfare weights calibrate agents' reported value scales. Independent affine
recodings preserve the weighted objective, up to an outcome-independent shift,
when each weight is divided by the corresponding scale factor. The identity
requires nonzero scale factors; positive factors additionally preserve each
agent's ranking of physical outcomes.

These objectives exclude transfers. Recoding a valuation alone does not recode
the corresponding quasilinear utility when monetary transfers stay fixed.
-/

@[expose] public section

universe uI uT uO

namespace MathEconLib.Mechanism

variable {I : Type uI} {T : I → Type uT} {O : Type uO}

namespace QuasilinearEnvironment

/-- Social value with explicitly supplied interpersonal welfare weights. -/
def weightedTotalValue [Fintype I] (E : QuasilinearEnvironment I T O)
    (weights : I → ℝ) (θ : Profile T) (o : O) : ℝ :=
  ∑ i, weights i * E.value i θ o

/-- The existing total value uses a weight of one for every agent. -/
@[simp] theorem weightedTotalValue_one [Fintype I] (E : QuasilinearEnvironment I T O)
    (θ : Profile T) (o : O) :
    E.weightedTotalValue (fun _ => 1) θ o = E.totalValue θ o := by
  simp only [weightedTotalValue, one_mul, totalValue]

/-- Reciprocal weight changes compensate independent affine recodings of value. -/
theorem weightedTotalValue_recode [Fintype I]
    {E E' : QuasilinearEnvironment I T O} {scale : I → ℝ}
    {offset : I → Profile T → ℝ} (nonzero : ∀ i, scale i ≠ 0)
    (recoded : ∀ i θ o, E'.value i θ o = scale i * E.value i θ o + offset i θ)
    (weights : I → ℝ) (θ : Profile T) (o : O) :
    E'.weightedTotalValue (fun i => weights i / scale i) θ o =
      E.weightedTotalValue weights θ o + ∑ i, weights i / scale i * offset i θ := by
  unfold weightedTotalValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [recoded i θ o, mul_add, ← mul_assoc, div_mul_cancel₀ _ (nonzero i)]

end QuasilinearEnvironment

namespace DirectMechanism

/-- Total-value efficiency can be expressed in independently recoded value units
using explicit reciprocal welfare weights. No property of transfers is asserted. -/
theorem isEfficient_iff_reciprocal_weighted [Fintype I]
    {E E' : QuasilinearEnvironment I T O} (M : DirectMechanism I T O)
    {scale : I → ℝ} {offset : I → Profile T → ℝ}
    (nonzero : ∀ i, scale i ≠ 0)
    (recoded : ∀ i θ o, E'.value i θ o = scale i * E.value i θ o + offset i θ) :
    IsEfficient E M ↔
      ∀ θ, IsMaxOn (E'.weightedTotalValue (fun i => 1 / scale i) θ)
        Set.univ (M.outcome θ) := by
  have normalized (θ : Profile T) (o : O) :
      E'.weightedTotalValue (fun i => 1 / scale i) θ o =
        E.totalValue θ o + ∑ i, 1 / scale i * offset i θ := by
    simpa only [QuasilinearEnvironment.weightedTotalValue_one] using
      QuasilinearEnvironment.weightedTotalValue_recode nonzero recoded (fun _ => 1) θ o
  simp only [IsEfficient, isMaxOn_iff, normalized, add_le_add_iff_right]

end DirectMechanism
end MathEconLib.Mechanism

end
