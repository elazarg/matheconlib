/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Averaging
public import MathEconLib.GameTheory.Strategic.Mixed
public import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Pure equilibria in the mixed extension

The Dirac embedding preserves pure Nash equilibrium for ordered vector payoffs.
Every admitted mixed deviation is integrable by the existing mixed-equilibrium
contract. Its product law is concentrated on unilateral pure deviations, so
ordered averaging applies without selecting one dominating pure action.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace MathEconLib.GameTheory.StrategicGame

variable {I : Type*} {A : I → Type*} {V : Type*} [Fintype I] [DecidableEq I]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V]

/-- A pure equilibrium remains a mixed equilibrium at its Dirac profile. The
conclusion compares precisely the integrable deviations admitted by `IsMixedNash`. -/
theorem IsNash.isMixedNash_dirac {G : StrategicGame I A V} {a : ∀ i, A i}
    (ha : G.IsNash a) : G.IsMixedNash (fun i ↦ diracProba (a i)) := by
  let σ : MixedStrategy A := fun i ↦ diracProba (a i)
  have hpure : ∀ᵐ b ∂Measure.pi (fun i ↦ (σ i : Measure (A i))), b = a := by
    filter_upwards [Measure.ae_eq_pi (μ := fun i ↦ Measure.dirac (a i))
      (fun i ↦ ae_eq_dirac (fun x : A i ↦ x))] with b hb
    exact hb
  have hpay (i : I) : G.payoff i =ᵐ[Measure.pi (fun j ↦ (σ j : Measure (A j)))]
      fun _ ↦ G.payoff i a := hpure.mono fun _ hb ↦ congrArg (G.payoff i) hb
  have hvalid : G.MixedPayoffsIntegrable σ := fun i ↦
    (integrable_congr (hpay i)).mpr (integrable_const _)
  have hvalue (i : I) : G.mixedExtension.payoff i σ = G.payoff i a := by
    change (∫ b, G.payoff i b ∂Measure.pi (fun j ↦ (σ j : Measure (A j)))) = _
    rw [integral_congr_ae (hpay i), integral_const]
    simp
  change G.mixedNashProblem.IsEquilibrium σ
  apply ha.of_integral_bounds id hvalid
  · intro i
    exact (hvalue i).ge
  · intro i σ' hσ'
    obtain ⟨⟨τ, rfl⟩, hint⟩ := hσ'
    let μ := ProbabilityMeasure.pi (Function.update σ i τ)
    refine ⟨μ, ?_, ?_, le_rfl⟩
    · exact hint
    · have hcoord : ∀ j, ∀ᵐ b ∂(μ : Measure (∀ j, A j)), j ≠ i → b j = a j := by
        intro j
        by_cases hj : j = i
        · exact ae_of_all _ fun _ hne ↦ (hne hj).elim
        · have hc : ∀ᵐ x ∂(Function.update σ i τ j : Measure (A j)), x = a j := by
            have he : Function.update σ i τ j = σ j := Function.update_of_ne hj τ σ
            rw [he]
            change ∀ᵐ x ∂Measure.dirac (a j), x = a j
            simp only [ae_dirac_eq, eventually_pure]
          exact (Measure.tendsto_eval_ae_ae (μ := fun j ↦
            (Function.update σ i τ j : Measure (A j))) (i := j)).eventually hc
            |>.mono fun _ hx _ ↦ hx
      filter_upwards [eventually_all.mpr hcoord] with b hb
      refine ⟨b i, ?_⟩
      funext j
      by_cases hj : j = i
      · subst j
        simp
      · exact (hb j hj).trans (Function.update_of_ne hj (b i) a).symm

end MathEconLib.GameTheory.StrategicGame
