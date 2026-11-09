/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Mixture

/-!
# Mixtures of incentive comparisons

Each comparison is a pair of prescribed and alternative outcome laws. A common
Markov kernel mixes both sides with the same weights. Ordered integral
inequalities are preserved when the actual target laws are integrable. This
does not require a common incumbent, a strategy compiler, or finite carriers.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathEconLib.GameTheory

universe u v w o

/-- A shared probability mixture representing both laws of a comparison. -/
structure ComparisonMixture {A : Type u} {B : Type v} {O : Type o}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace O]
    (sourcePrescribed sourceAlternative : Kernel A O)
    (targetPrescribed targetAlternative : Kernel B O) where
  /-- Shared randomization over source comparisons. -/
  mixing : Kernel B A
  /-- Mixture weights have total mass one. -/
  isMarkov_mixing : IsMarkovKernel mixing
  /-- The mixture reproduces the prescribed law. -/
  prescribed_eq : sourcePrescribed ∘ₖ mixing = targetPrescribed
  /-- The same mixture reproduces the alternative law. -/
  alternative_eq : sourceAlternative ∘ₖ mixing = targetAlternative

attribute [instance] ComparisonMixture.isMarkov_mixing

namespace ComparisonMixture

variable {A : Type u} {B : Type v} {C : Type w} {O : Type o}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace O]
    {AP AQ : Kernel A O} {BP BQ : Kernel B O} {CP CQ : Kernel C O}

/-- The identity comparison mixture. -/
def id (P Q : Kernel A O) : ComparisonMixture P Q P Q where
  mixing := Kernel.id
  isMarkov_mixing := inferInstance
  prescribed_eq := Kernel.comp_id _
  alternative_eq := Kernel.comp_id _

/-- Composition retains the joint mixture witnesses for both laws. -/
def comp (g : ComparisonMixture BP BQ CP CQ) (f : ComparisonMixture AP AQ BP BQ) :
    ComparisonMixture AP AQ CP CQ where
  mixing := f.mixing ∘ₖ g.mixing
  isMarkov_mixing := inferInstance
  prescribed_eq := by rw [← Kernel.comp_assoc, f.prescribed_eq, g.prescribed_eq]
  alternative_eq := by rw [← Kernel.comp_assoc, f.alternative_eq, g.alternative_eq]

/-- Equality of selected mixing kernels determines the certificate. -/
@[ext] theorem ext {f g : ComparisonMixture AP AQ BP BQ} (h : f.mixing = g.mixing) : f = g := by
  cases f
  cases g
  cases h
  rfl

@[simp] theorem id_comp (f : ComparisonMixture AP AQ BP BQ) : (id BP BQ).comp f = f :=
  ext (Kernel.comp_id _)

@[simp] theorem comp_id (f : ComparisonMixture AP AQ BP BQ) : f.comp (id AP AQ) = f :=
  ext (Kernel.id_comp _)

/-- Comparison mixtures compose associatively. -/
theorem comp_assoc {D : Type*} [MeasurableSpace D] {DP DQ : Kernel D O}
    (h : ComparisonMixture CP CQ DP DQ) (g : ComparisonMixture BP BQ CP CQ)
    (f : ComparisonMixture AP AQ BP BQ) : (h.comp g).comp f = h.comp (g.comp f) :=
  ext (Kernel.comp_assoc _ _ _).symm

/-- Integral inequalities need hold only almost surely under the selected
mixture. Integrability is required on the two actual target laws. -/
theorem preserves_at {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V]
    (f : ComparisonMixture AP AQ BP BQ) (u : O → V) (b : B)
    (hp : Integrable u (BP b)) (hq : Integrable u (BQ b))
    (h : ∀ᵐ a ∂f.mixing b, (∫ o, u o ∂AQ a) ≤ ∫ o, u o ∂AP a) :
    (∫ o, u o ∂BQ b) ≤ ∫ o, u o ∂BP b := by
  have hp' : Integrable u ((AP ∘ₖ f.mixing) b) := f.prescribed_eq.symm ▸ hp
  have hq' : Integrable u ((AQ ∘ₖ f.mixing) b) := f.alternative_eq.symm ▸ hq
  calc
    _ = ∫ o, u o ∂(AQ ∘ₖ f.mixing) b :=
      congrArg (fun K : Kernel B O ↦ ∫ o, u o ∂K b) f.alternative_eq.symm
    _ = ∫ a, ∫ o, u o ∂AQ a ∂f.mixing b := Kernel.integral_comp hq'
    _ ≤ ∫ a, ∫ o, u o ∂AP a ∂f.mixing b :=
      integral_mono_ae hq'.integral_comp hp'.integral_comp h
    _ = ∫ o, u o ∂(AP ∘ₖ f.mixing) b := (Kernel.integral_comp hp').symm
    _ = _ := congrArg (fun K : Kernel B O ↦ ∫ o, u o ∂K b) f.prescribed_eq

end ComparisonMixture

namespace MixtureSimulation

variable {S : Type u} {T : Type v} {I J : Type*} {O : Type o}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    {DP : I → S → S → Prop} {DQ : J → T → T → Prop}
    {LP : Kernel S O} {LQ : Kernel T O}

/-- At a fixed incumbent and deviator, a deviation simulation is a mixture of
comparisons with constant prescribed law. The target index records legality. -/
def toComparisonMixture (f : MixtureSimulation DP DQ LP LQ) (j : J) (s : S) :
    ComparisonMixture (Kernel.const S (LP s)) LP
      (Kernel.const {t // DQ j (f.toFun s) t} (LQ (f.toFun s)))
      (LQ.comap Subtype.val measurable_subtype_coe) where
  mixing := (f.simulate j s).comap Subtype.val measurable_subtype_coe
  isMarkov_mixing := inferInstance
  prescribed_eq := by rw [Kernel.const_comp', f.honest_law]
  alternative_eq := by
    apply Kernel.ext
    intro t
    change (LP ∘ₖ f.simulate j s) t.val = LQ t.val
    exact f.deviation_law j s t.val t.property

end MixtureSimulation

end MathEconLib.GameTheory
