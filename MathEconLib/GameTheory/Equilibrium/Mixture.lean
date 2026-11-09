/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Averaging
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# Utility-independent simulations by mixtures of source deviations

The source and target laws are Mathlib kernels on arbitrary measurable spaces.
A selected Markov kernel simulates each target deviation by a probability law
on legal source deviations. Honest observed laws agree. Identity and composition
retain the mixture witnesses. Ordered integral evaluation transports optimality;
scalar evaluation also constructs a `GameSimulation`.

Deviation relations and law kernels are explicit parameters, so the same
certificate can serve different utility evaluations and equilibrium problems.
Measurability of source deviation sets is required by composition, not stored
in every bare relation. A measurable exact lift gives a deterministic mixture.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace MathEconLib.GameTheory

universe u v w x y z o

/-- A player-reindexed state translation with honest-law equality and a Markov
kernel representing each target deviation by legal source deviations. -/
structure MixtureSimulation {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    {O : Type o} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    (sourceDeviation : I → S → S → Prop) (targetDeviation : J → T → T → Prop)
    (sourceLaw : Kernel S O) (targetLaw : Kernel T O) where
  /-- Translate source incumbent states. -/
  toFun : S → T
  /-- The source deviator corresponding to each target deviator. -/
  deviatorMap : J → I
  /-- The selected probability kernel on source alternatives. -/
  simulate : J → S → Kernel T S
  /-- Simulation uses probability laws, including outside admitted deviations. -/
  isMarkov_simulate : ∀ j s, IsMarkovKernel (simulate j s)
  /-- Honest compilation preserves the common observed law. -/
  honest_law : ∀ s, targetLaw (toFun s) = sourceLaw s
  /-- Simulated alternatives are legal source deviations almost surely. -/
  deviation_ae : ∀ j s t, targetDeviation j (toFun s) t →
    ∀ᵐ s' ∂simulate j s t, sourceDeviation (deviatorMap j) s s'
  /-- Mixing source laws exactly reproduces the target deviation law. -/
  deviation_law : ∀ j s t, targetDeviation j (toFun s) t →
    (sourceLaw ∘ₖ simulate j s) t = targetLaw t

attribute [instance] MixtureSimulation.isMarkov_simulate

namespace MixtureSimulation

variable {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    {U : Type y} {K : Type z} {O : Type o}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace O]
    {DP : I → S → S → Prop} {DQ : J → T → T → Prop} {DR : K → U → U → Prop}
    {LP : Kernel S O} {LQ : Kernel T O} {LR : Kernel U O}

/-- Identity simulation. Measurable deviation sets make their pointwise truth
at a Dirac atom equivalent to their almost-sure truth. -/
def id (D : I → S → S → Prop) (L : Kernel S O)
    (hD : ∀ i s, MeasurableSet {s' | D i s s'}) : MixtureSimulation D D L L where
  toFun := _root_.id
  deviatorMap := _root_.id
  simulate _ _ := Kernel.id
  isMarkov_simulate _ _ := inferInstance
  honest_law _ := rfl
  deviation_ae i s t ht := by
    change ∀ᵐ s' ∂Measure.dirac t, D i s s'
    exact (ae_dirac_iff (hD i s)).mpr ht
  deviation_law _ _ _ _ := by simp

/-- Measurable simulation kernels compose by kernel composition. Only source
deviation-set measurability is needed to propagate almost-sure legality. -/
def comp (g : MixtureSimulation DQ DR LQ LR) (f : MixtureSimulation DP DQ LP LQ)
    (hDP : ∀ i s, MeasurableSet {s' | DP i s s'}) : MixtureSimulation DP DR LP LR where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := f.deviatorMap ∘ g.deviatorMap
  simulate k s := f.simulate (g.deviatorMap k) s ∘ₖ g.simulate k (f.toFun s)
  isMarkov_simulate _ _ := inferInstance
  honest_law s := (g.honest_law (f.toFun s)).trans (f.honest_law s)
  deviation_ae k s t ht := by
    apply Kernel.ae_comp_of_ae_ae (hDP _ _)
    filter_upwards [g.deviation_ae k (f.toFun s) t ht] with q hq
    exact f.deviation_ae (g.deviatorMap k) s q hq
  deviation_law k s t ht := by
    rw [← Kernel.comp_assoc, Kernel.comp_apply]
    calc
      _ = (LQ ∘ₖ g.simulate k (f.toFun s)) t := by
        apply Measure.bind_congr_right
        filter_upwards [g.deviation_ae k (f.toFun s) t ht] with q hq
        exact f.deviation_law (g.deviatorMap k) s q hq
      _ = LR t := g.deviation_law k (f.toFun s) t ht

/-- A measurable deterministic exact lift is a one-point mixture. -/
def ofExactLifts (f : S → T) (g : J → I)
    (lift : J → S → T → S) (hlift : ∀ j s, Measurable (lift j s))
    (hDP : ∀ i s, MeasurableSet {s' | DP i s s'})
    (hhonest : ∀ s, LQ (f s) = LP s)
    (hlegal : ∀ j s t, DQ j (f s) t → DP (g j) s (lift j s t))
    (hexact : ∀ j s t, DQ j (f s) t → f (lift j s t) = t) :
    MixtureSimulation DP DQ LP LQ where
  toFun := f
  deviatorMap := g
  simulate j s := Kernel.deterministic (lift j s) (hlift j s)
  isMarkov_simulate _ _ := inferInstance
  honest_law := hhonest
  deviation_ae j s t ht := by
    change ∀ᵐ s' ∂Measure.dirac (lift j s t), DP (g j) s s'
    exact (ae_dirac_iff (hDP _ _)).mpr (hlegal j s t ht)
  deviation_law j s t ht := by
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
    rw [← hhonest, hexact j s t ht]

/-- Certificates agree when all their selected data agree. -/
@[ext] theorem ext {f g : MixtureSimulation DP DQ LP LQ}
    (hf : f.toFun = g.toFun) (hg : f.deviatorMap = g.deviatorMap)
    (hk : f.simulate = g.simulate) : f = g := by
  cases f
  cases g
  cases hf
  cases hg
  cases hk
  rfl

@[simp] theorem id_comp (f : MixtureSimulation DP DQ LP LQ)
    (hDP : ∀ i s, MeasurableSet {s' | DP i s s'})
    (hDQ : ∀ j t, MeasurableSet {t' | DQ j t t'}) :
    (id DQ LQ hDQ).comp f hDP = f := by
  apply ext (f := (id DQ LQ hDQ).comp f hDP) (g := f) rfl rfl
  funext j s
  exact Kernel.comp_id _

@[simp] theorem comp_id (f : MixtureSimulation DP DQ LP LQ)
    (hDP : ∀ i s, MeasurableSet {s' | DP i s s'}) :
    f.comp (id DP LP hDP) hDP = f := by
  apply ext (f := f.comp (id DP LP hDP) hDP) (g := f) rfl rfl
  funext j s
  exact Kernel.id_comp _

/-- Kernel associativity makes staged simulation independent of parentheses. -/
theorem comp_assoc {A B : Type*} [MeasurableSpace A] {DA : B → A → A → Prop}
    {LA : Kernel A O} (h : MixtureSimulation DR DA LR LA)
    (g : MixtureSimulation DQ DR LQ LR) (f : MixtureSimulation DP DQ LP LQ)
    (hDP : ∀ i s, MeasurableSet {s' | DP i s s'})
    (hDQ : ∀ j t, MeasurableSet {t' | DQ j t t'}) :
    (h.comp g hDQ).comp f hDP = h.comp (g.comp f hDP) hDP := by
  apply ext (f := (h.comp g hDQ).comp f hDP) (g := h.comp (g.comp f hDP) hDP) rfl rfl
  funext j s
  exact (Kernel.comp_assoc _ _ _).symm

/-- Observing outcomes preserves the same deviation-mixture witnesses. -/
def mapOutcome {O' : Type*} [MeasurableSpace O']
    (f : MixtureSimulation DP DQ LP LQ) (observe : O → O') (ho : Measurable observe) :
    MixtureSimulation DP DQ (LP.map observe) (LQ.map observe) where
  toFun := f.toFun
  deviatorMap := f.deviatorMap
  simulate := f.simulate
  isMarkov_simulate := f.isMarkov_simulate
  honest_law s := by
    rw [Kernel.map_apply _ ho, Kernel.map_apply _ ho, f.honest_law]
  deviation_ae := f.deviation_ae
  deviation_law j s t ht := by
    rw [← Kernel.map_comp, Kernel.map_apply _ ho, f.deviation_law j s t ht,
      Kernel.map_apply _ ho]

section Evaluation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : MixtureSimulation DP DQ LP LQ)
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    (u : I → O → V)
    (hP : ∀ i s, P.value i s = ∫ o, u i o ∂LP s)
    (hQ : ∀ j t, Q.value j t = ∫ o, u (f.deviatorMap j) o ∂LQ t)

include hP hQ

/-- Honest-law agreement gives exact incumbent values under matching evaluation. -/
theorem value_eq (s : S) (j : J) : Q.value j (f.toFun s) = P.value (f.deviatorMap j) s := by
  rw [hQ, f.honest_law, hP]

/-- An integrable target law gives an integrable mixture of source values,
supported on admissible deviations, with the same target value. -/
theorem integral_representation (hDP : P.deviation = DP) {j : J} {s : S} {t : T}
    (ht : DQ j (f.toFun s) t) (hint : Integrable (u (f.deviatorMap j)) (LQ t)) :
    ∃ μ : ProbabilityMeasure S, Integrable (P.value (f.deviatorMap j)) μ ∧
      (∀ᵐ s' ∂(μ : Measure S), P.deviation (f.deviatorMap j) s s') ∧
      Q.value j t = ∫ s', P.value (f.deviatorMap j) s' ∂(μ : Measure S) := by
  have hi : Integrable (u (f.deviatorMap j)) ((LP ∘ₖ f.simulate j s) t) :=
    (f.deviation_law j s t ht).symm ▸ hint
  have heval : P.value (f.deviatorMap j) =
      fun s' ↦ ∫ o, u (f.deviatorMap j) o ∂LP s' :=
    funext (hP (f.deviatorMap j))
  refine ⟨⟨f.simulate j s t, inferInstance⟩, ?_, ?_, ?_⟩
  · simpa only [ProbabilityMeasure.coe_mk, heval] using hi.integral_comp
  · simpa only [ProbabilityMeasure.coe_mk, hDP] using f.deviation_ae j s t ht
  · simp only [ProbabilityMeasure.coe_mk]
    rw [hQ, ← f.deviation_law j s t ht, Kernel.integral_comp hi,
      heval]

variable [CompleteSpace V] [PartialOrder V] [IsOrderedAddMonoid V]
    [IsOrderedModule ℝ V] [ClosedIciTopology V]

/-- Ordered integral evaluation transports optimality without scalarizing payoffs. -/
theorem transport_isDeviationOptimal (hDP : P.deviation = DP) (hDQ : Q.deviation = DQ)
    (hdev : ∀ j s t, DQ j (f.toFun s) t → Integrable (u (f.deviatorMap j)) (LQ t))
    {s : S} (hs : P.IsDeviationOptimal s) : Q.IsDeviationOptimal (f.toFun s) := by
  apply hs.of_integral_bounds f.deviatorMap
  · intro j
    exact (f.value_eq u hP hQ s j).symm.le
  · intro j t ht
    have ht' : DQ j (f.toFun s) t := hDQ ▸ ht
    obtain ⟨μ, hi, hd, he⟩ := f.integral_representation u hP hQ hDP ht' (hdev j s t ht')
    exact ⟨μ, hi, hd, he.le⟩

/-- Full equilibrium transport additionally preserves candidate validity. -/
theorem transport (hDP : P.deviation = DP) (hDQ : Q.deviation = DQ)
    (hvalid : ∀ s, P.valid s → Q.valid (f.toFun s))
    (hdev : ∀ j s t, DQ j (f.toFun s) t → Integrable (u (f.deviatorMap j)) (LQ t))
    {s : S} (hs : P.IsEquilibrium s) : Q.IsEquilibrium (f.toFun s) :=
  ⟨hvalid s hs.valid, f.transport_isDeviationOptimal u hP hQ hDP hDQ hdev hs.deviation_le⟩

end Evaluation

/-- A real utility on an integrable simulated law has one legal source
deviation with integrable utility and value at least the target's value. -/
theorem exists_source_deviation_ge (f : MixtureSimulation DP DQ LP LQ)
    (u : I → O → ℝ) {j : J} {s : S} {t : T} (ht : DQ j (f.toFun s) t)
    (hint : Integrable (u (f.deviatorMap j)) (LQ t)) :
    ∃ s', DP (f.deviatorMap j) s s' ∧ Integrable (u (f.deviatorMap j)) (LP s') ∧
      (∫ o, u (f.deviatorMap j) o ∂LQ t) ≤ ∫ o, u (f.deviatorMap j) o ∂LP s' := by
  have hi : Integrable (u (f.deviatorMap j)) ((LP ∘ₖ f.simulate j s) t) :=
    (f.deviation_law j s t ht).symm ▸ hint
  have hgood := (f.deviation_ae j s t ht).and hi.ae_of_comp
  obtain ⟨s', hs', hmean⟩ :=
    exists_notMem_null_integral_le hi.integral_comp (ae_iff.mp hgood)
  have hs : DP (f.deviatorMap j) s s' ∧ Integrable (u (f.deviatorMap j)) (LP s') := by
    simpa using hs'
  refine ⟨s', hs.1, hs.2, ?_⟩
  rw [← f.deviation_law j s t ht, Kernel.integral_comp hi]
  exact hmean

/-- Real utility evaluation converts a law-mixture certificate to a simulation
by selecting an admissible source deviation whose value is at least its mean. -/
def toSimulation (f : MixtureSimulation DP DQ LP LQ)
    {P : EquilibriumProblem S I ℝ} {Q : EquilibriumProblem T J ℝ}
    (u : I → O → ℝ)
    (hP : ∀ i s, P.value i s = ∫ o, u i o ∂LP s)
    (hQ : ∀ j t, Q.value j t = ∫ o, u (f.deviatorMap j) o ∂LQ t)
    (hDP : P.deviation = DP) (hDQ : Q.deviation = DQ)
    (hvalid : ∀ s, P.valid s → Q.valid (f.toFun s))
    (hdev : ∀ j s t, DQ j (f.toFun s) t → Integrable (u (f.deviatorMap j)) (LQ t)) :
    GameSimulation P Q where
  toFun := f.toFun
  deviatorMap := f.deviatorMap
  value_le j s := (f.value_eq u hP hQ s j).symm.le
  valid_preserves := hvalid
  deviation_dominated j s t ht := by
    have ht' : DQ j (f.toFun s) t := hDQ ▸ ht
    obtain ⟨s', hd, _, hb⟩ := f.exists_source_deviation_ge u ht' (hdev j s t ht')
    refine ⟨s', hDP.symm ▸ hd, ?_⟩
    simpa only [hP, hQ] using hb

end MixtureSimulation

namespace GameMorphism

variable {S : Type u} {I : Type v} {T : Type w} {J : Type x} {O : Type o} {V : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace O]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}

/-- On a discrete target measurable space, exact lifts can be chosen measurably.
Honest observed-law equality is a separate hypothesis from reward preservation. -/
def toMixtureSimulation [DiscreteMeasurableSpace T] (f : GameMorphism P Q)
    (LP : Kernel S O) (LQ : Kernel T O)
    (hDP : ∀ i s, MeasurableSet {s' | P.deviation i s s'})
    (hhonest : ∀ s, LQ (f.toFun s) = LP s) :
    MixtureSimulation P.deviation Q.deviation LP LQ := by
  classical
  let lift := fun j s t ↦ if h : Q.deviation j (f.toFun s) t then
    (f.deviation_lifts j s t h).choose else s
  refine MixtureSimulation.ofExactLifts f.toFun f.deviatorMap lift
    (fun _ _ ↦ Measurable.of_discrete) hDP hhonest ?_ ?_
  · intro j s t ht
    simpa only [lift, dite_eq_left ht] using (f.deviation_lifts j s t ht).choose_spec.1
  · intro j s t ht
    simpa only [lift, dite_eq_left ht] using (f.deviation_lifts j s t ht).choose_spec.2

end GameMorphism

end MathEconLib.GameTheory
