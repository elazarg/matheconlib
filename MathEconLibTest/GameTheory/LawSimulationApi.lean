/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib

/-!
# Law simulation and expected-utility API pins

Each `example` restates the full type of a public declaration and proves it by the declaration
itself, as in `ApiStability.lean`. The only project import is the public root `MathEconLib`, so
these checks also cover the export boundary. The pins cover expected-utility problems, averaging,
comparison and law mixtures, their strategic clients, and the multi-agent revelation principles.

The two record checks at the end fix the pure and mixed Nash problems definitionally, so that
later refactors toward the shared expected-utility construction cannot change their meaning.
-/

-- This module only contains `example`s, which are never public.
set_option linter.privateModule false

noncomputable section

open MathEconLib MathEconLib.GameTheory MathEconLib.Probability MathEconLib.Mechanism
open MeasureTheory ProbabilityTheory

namespace MathEconLibTest.GameTheory.LawSimulationApi

/-! ## Expected-utility problems -/

example : {S : Type*} → {I : Type*} → {O : Type*} → {V : Type*} → [MeasurableSpace O] →
    [NormedAddCommGroup V] → [NormedSpace ℝ V] → [CompleteSpace V] → (I → S → S → Prop) → (S →
    Measure O) → (I → O → V) → EquilibriumProblem S I V :=
  @EquilibriumProblem.ofExpectedValue

example : ∀ {S : Type*} {I : Type*} {O : Type*} [MeasurableSpace O] (D : I → S → S → Prop) (L : S →
    Measure O) [∀ (s : S), IsProbabilityMeasure (L s)] (u : I → O → ℝ) (a c : I → ℝ), (∀ (i : I), 0
    < a i) → ∀ (s : S), (EquilibriumProblem.ofExpectedValue D L fun (i : I) (o : O) => a i * u i o +
    c i).IsEquilibrium s ↔ (EquilibriumProblem.ofExpectedValue D L u).IsEquilibrium s :=
  @EquilibriumProblem.isEquilibrium_ofExpectedValue_affine_iff

/-! ## Averaging -/

example : ∀ {S : Type*} {I : Type*} {T : Type*} {J : Type*} {V : Type*} [MeasurableSpace S]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [PartialOrder V] [IsOrderedAddMonoid
    V] [IsOrderedModule ℝ V] [ClosedIciTopology V] {P : EquilibriumProblem S I V} {Q :
    EquilibriumProblem T J V} {s : S} {t : T}, P.IsEquilibrium s → ∀ (g : J → I), Q.valid t → (∀ (j
    : J), P.value (g j) s ≤ Q.value j t) → (∀ (j : J) (t' : T), Q.deviation j t t' → ∃ (μ :
    ProbabilityMeasure S), Integrable (P.value (g j)) (μ : Measure S) ∧ (∀ᵐ (s' : S) ∂(μ : Measure
    S), P.deviation (g j) s s') ∧ Q.value j t' ≤ ∫ (s' : S), P.value (g j) s' ∂(μ : Measure S)) →
    Q.IsEquilibrium t :=
  @EquilibriumProblem.IsEquilibrium.of_integral_bounds

example : {S : Type*} → {I : Type*} → {T : Type*} → {J : Type*} → [MeasurableSpace S] → {P :
    EquilibriumProblem S I ℝ} → {Q : EquilibriumProblem T J ℝ} → (f : S → T) → (g : J → I) → (∀ (j :
    J) (s : S), P.value (g j) s ≤ Q.value j (f s)) → (∀ (s : S), P.valid s → Q.valid (f s)) → (∀ (j
    : J) (s : S) (t : T), Q.deviation j (f s) t → ∃ (μ : ProbabilityMeasure S), Integrable (P.value
    (g j)) (μ : Measure S) ∧ (∀ᵐ (s' : S) ∂(μ : Measure S), P.deviation (g j) s s') ∧ Q.value j t ≤
    ∫ (s' : S), P.value (g j) s' ∂(μ : Measure S)) → GameSimulation P Q :=
  @GameSimulation.ofIntegralBounds

/-! ## Comparison and law mixtures -/

example : ∀ {A : Type*} {B : Type*} {O : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace O] {AP AQ : Kernel A O} {BP BQ : Kernel B O} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ
    V] [ClosedIciTopology V] (f : ComparisonMixture AP AQ BP BQ) (u : O → V) (b : B), Integrable u
    (BP b) → Integrable u (BQ b) → (∀ᵐ (a : A) ∂f.mixing b, ∫ (o : O), u o ∂AQ a ≤ ∫ (o : O), u o
    ∂AP a) → ∫ (o : O), u o ∂BQ b ≤ ∫ (o : O), u o ∂BP b :=
  @ComparisonMixture.preserves_at

example : {S : Type*} → {I : Type*} → {T : Type*} → {J : Type*} → {O : Type*} → [MeasurableSpace S]
    → [MeasurableSpace T] → [MeasurableSpace O] → {sourceDeviation : I → S → S → Prop} →
    {targetDeviation : J → T → T → Prop} → {sourceLaw : Kernel S O} → {targetLaw : Kernel T O} →
    (toFun : S → T) → (deviatorMap : J → I) → (simulate : J → S → Kernel T S) → (∀ (j : J) (s : S),
    IsMarkovKernel (simulate j s)) → (∀ (s : S), targetLaw (toFun s) = sourceLaw s) → (∀ (j : J) (s
    : S) (t : T), targetDeviation j (toFun s) t → ∀ᵐ (s' : S) ∂(simulate j s) t, sourceDeviation
    (deviatorMap j) s s') → (∀ (j : J) (s : S) (t : T), targetDeviation j (toFun s) t → (sourceLaw
    ∘ₖ simulate j s) t = targetLaw t) → MixtureSimulation sourceDeviation targetDeviation sourceLaw
    targetLaw :=
  @MixtureSimulation.mk

example : {S : Type*} → {I : Type*} → {O : Type*} → [MeasurableSpace S] → [MeasurableSpace O] → (D :
    I → S → S → Prop) → (L : Kernel S O) → (∀ (i : I) (s : S), MeasurableSet {s' : S | D i s s'}) →
    MixtureSimulation D D L L :=
  @MixtureSimulation.id

example : {S : Type*} → {I : Type*} → {T : Type*} → {J : Type*} → {U : Type*} → {K : Type*} → {O :
    Type*} → [MeasurableSpace S] → [MeasurableSpace T] → [MeasurableSpace U] → [MeasurableSpace O] →
    {DP : I → S → S → Prop} → {DQ : J → T → T → Prop} → {DR : K → U → U → Prop} → {LP : Kernel S O}
    → {LQ : Kernel T O} → {LR : Kernel U O} → MixtureSimulation DQ DR LQ LR → MixtureSimulation DP
    DQ LP LQ → (∀ (i : I) (s : S), MeasurableSet {s' : S | DP i s s'}) → MixtureSimulation DP DR LP
    LR :=
  @MixtureSimulation.comp

example : {S : Type*} → {I : Type*} → {T : Type*} → {J : Type*} → {O : Type*} → [MeasurableSpace S]
    → [MeasurableSpace T] → [MeasurableSpace O] → {DP : I → S → S → Prop} → {DQ : J → T → T → Prop}
    → {LP : Kernel S O} → {LQ : Kernel T O} → (f : S → T) → (g : J → I) → (lift : J → S → T → S) →
    (∀ (j : J) (s : S), Measurable (lift j s)) → (∀ (i : I) (s : S), MeasurableSet {s' : S | DP i s
    s'}) → (∀ (s : S), LQ (f s) = LP s) → (∀ (j : J) (s : S) (t : T), DQ j (f s) t → DP (g j) s
    (lift j s t)) → (∀ (j : J) (s : S) (t : T), DQ j (f s) t → f (lift j s t) = t) →
    MixtureSimulation DP DQ LP LQ :=
  @MixtureSimulation.ofExactLifts

example : ∀ {S : Type*} {I : Type*} {T : Type*} {J : Type*} {O : Type*} [MeasurableSpace S]
    [MeasurableSpace T] [MeasurableSpace O] {DP : I → S → S → Prop} {DQ : J → T → T → Prop} {LP :
    Kernel S O} {LQ : Kernel T O} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f :
    MixtureSimulation DP DQ LP LQ) {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V} (u
    : I → O → V), (∀ (i : I) (s : S), P.value i s = ∫ (o : O), u i o ∂LP s) → (∀ (j : J) (t : T),
    Q.value j t = ∫ (o : O), u (f.deviatorMap j) o ∂LQ t) → ∀ [CompleteSpace V] [PartialOrder V]
    [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V] {s : S}, (∀ (j : J) (s' : S),
    DP (f.deviatorMap j) s s' → Integrable (u (f.deviatorMap j)) (LP s') → P.deviation
    (f.deviatorMap j) s s') → (∀ (j : J) (t : T), Q.deviation j (f.toFun s) t → DQ j (f.toFun s) t)
    → Q.valid (f.toFun s) → (∀ (j : J) (t : T), Q.deviation j (f.toFun s) t → Integrable (u
    (f.deviatorMap j)) (LQ t)) → P.IsEquilibrium s → Q.IsEquilibrium (f.toFun s) :=
  @MixtureSimulation.transport

example : {S : Type*} → {I : Type*} → {T : Type*} → {J : Type*} → {O : Type*} → [MeasurableSpace S]
    → [MeasurableSpace T] → [MeasurableSpace O] → {DP : I → S → S → Prop} → {DQ : J → T → T → Prop}
    → {LP : Kernel S O} → {LQ : Kernel T O} → (f : MixtureSimulation DP DQ LP LQ) → {P :
    EquilibriumProblem S I ℝ} → {Q : EquilibriumProblem T J ℝ} → (u : I → O → ℝ) → (∀ (i : I) (s :
    S), P.value i s = ∫ (o : O), u i o ∂LP s) → (∀ (j : J) (t : T), Q.value j t = ∫ (o : O), u
    (f.deviatorMap j) o ∂LQ t) → (∀ (j : J) (s s' : S), DP (f.deviatorMap j) s s' → Integrable (u
    (f.deviatorMap j)) (LP s') → P.deviation (f.deviatorMap j) s s') → (∀ (j : J) (s : S) (t : T),
    Q.deviation j (f.toFun s) t → DQ j (f.toFun s) t) → (∀ (s : S), P.valid s → Q.valid (f.toFun s))
    → (∀ (j : J) (s : S) (t : T), Q.deviation j (f.toFun s) t → Integrable (u (f.deviatorMap j)) (LQ
    t)) → GameSimulation P Q :=
  @MixtureSimulation.toSimulation

example : ∀ {S : Type*} {I : Type*} {T : Type*} {J : Type*} {O : Type*} [MeasurableSpace S]
    [MeasurableSpace T] [MeasurableSpace O] {DP : I → S → S → Prop} {DQ : J → T → T → Prop} {LP :
    Kernel S O} {LQ : Kernel T O} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ V]
    [ClosedIciTopology V] (f : MixtureSimulation DP DQ LP LQ) (u : I → O → V) {s : S},
    (EquilibriumProblem.ofExpectedValue DP (⇑LP) u).IsEquilibrium s →
    (EquilibriumProblem.ofExpectedValue DQ (⇑LQ) (u ∘ f.deviatorMap)).IsEquilibrium (f.toFun s) :=
  @MixtureSimulation.transport_ofExpectedValue

/-! ## Strategic clients -/

example : ∀ {I : Type*} {J : Type*} {O : Type*} {V : Type*} {A : I → Type*} {B : J → Type*}
    [DecidableEq I] [DecidableEq J] [(i : I) → MeasurableSpace (A i)] [(j : J) → MeasurableSpace (B
    j)] [MeasurableSpace O] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [PartialOrder
    V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V] {G : OutcomeGame I A
    (ProbabilityMeasure O)} {H : OutcomeGame J B (ProbabilityMeasure O)} [G.Measurable]
    [H.Measurable] (f : MixtureSimulation IsUnilateralDeviation IsUnilateralDeviation G.toKernel
    H.toKernel) (P : PayoffStructure I O V) {a : (i : I) → A i}, (G.expectedNashProblem
    P).IsEquilibrium a → (H.expectedNashProblem (P.reindex f.deviatorMap)).IsEquilibrium (f.toFun a)
    :=
  @MixtureSimulation.transport_expectedNash

example : ∀ {I : Type*} {A : I → Type*} {V : Type*} [Fintype I] [DecidableEq I] [(i : I) →
    MeasurableSpace (A i)] [∀ (i : I), MeasurableSingletonClass (A i)] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ
    V] [ClosedIciTopology V] {G : StrategicGame I A V} {a : (i : I) → A i}, G.IsNash a →
    G.IsMixedNash fun (i : I) => diracProba (a i) :=
  @StrategicGame.IsNash.isMixedNash_dirac

example : ∀ {I : Type*} {J : Type*} {V : Type*} {A : I → Type*} {B : J → Type*} [Fintype I]
    [DecidableEq I] [DecidableEq J] [(i : I) → MeasurableSpace (A i)] [(j : J) → MeasurableSpace (B
    j)] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [PartialOrder V]
    [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V] {G : StrategicGame I A V} {H
    : OutcomeGame J B (ProbabilityMeasure ((i : I) → A i))} [H.Measurable] (f : MixtureSimulation
    IsUnilateralDeviation IsUnilateralDeviation G.outcomeGame.mixed.toKernel H.toKernel) {σ :
    StrategicGame.MixedStrategy A}, G.IsMixedNash σ → (H.expectedNashProblem
    (G.payoffStructure.reindex f.deviatorMap)).IsEquilibrium (f.toFun σ) :=
  @MixtureSimulation.transport_isMixedNash

/-! ## Revelation principles -/

example : ∀ {I : Type*} {T : I → Type*} {A : I → Type*} {O : Type*} (M : Mechanism I A O) (E :
    QuasilinearEnvironment I T O) [DecidableEq I] (σ : (i : I) → T i → A i), (∀ (θ : Profile T) (i :
    I), StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (i := i) (σ i (θ i))) →
    DirectMechanism.IsDSIC E (M.comap σ) :=
  @MathEconLib.Mechanism.isDSIC_comap_of_isDominant

example : ∀ {I : Type*} {T : I → Type*} {A : I → Type*} {O : Type*} (M : Mechanism I A O) (E :
    QuasilinearEnvironment I T O) [DecidableEq I] (σ : (i : I) → T i → A i), (∀ (θ : Profile T) (i :
    I), StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (i := i) (σ i (θ i))) → ∃ (D :
    DirectMechanism I T O), DirectMechanism.IsDSIC E D ∧ (∀ (θ : Profile T), D.outcome θ = M.outcome
    fun (i : I) => σ i (θ i)) ∧ ∀ (i : I) (θ : Profile T), D.transfer i θ = M.transfer i fun (j : I)
    => σ j (θ j) :=
  @MathEconLib.Mechanism.revelation_principle_dominant

example : ∀ {I : Type*} {T : I → Type*} {A : I → Type*} {O : Type*} (M : Mechanism I A O) (E :
    QuasilinearEnvironment I T O) [(i : I) → MeasurableSpace (T i)] [(i : I) → MeasurableSpace (A
    i)] (μ : Measure (Profile T)) [IsProbabilityMeasure μ] (σ : (M.inducedBayesianGame E).Strategy),
    (M.inducedBayesianGame E).IsBNE μ σ → ((M.comap fun (i : I) => (σ i).1).inducedBayesianGame
    E).IsBNE μ (DirectMechanism.Quasilinear.truthfulStrategy E (M.comap fun (i : I) => (σ i).1)) :=
  @MathEconLib.Mechanism.isBNE_truthful_comap

example : ∀ {I : Type*} {T : I → Type*} {A : I → Type*} {O : Type*} (M : Mechanism I A O) (E :
    QuasilinearEnvironment I T O) [(i : I) → MeasurableSpace (T i)] [(i : I) → MeasurableSpace (A
    i)] (μ : Measure (Profile T)) [IsProbabilityMeasure μ] (σ : (M.inducedBayesianGame E).Strategy),
    (M.inducedBayesianGame E).IsBNE μ σ → ∃ (D : DirectMechanism I T O), (inducedBayesianGame D
    E).IsBNE μ (DirectMechanism.Quasilinear.truthfulStrategy E D) ∧ (∀ (θ : Profile T), D.outcome θ
    = M.outcome fun (i : I) => (σ i).1 (θ i)) ∧ ∀ (i : I) (θ : Profile T), D.transfer i θ =
    M.transfer i fun (j : I) => (σ j).1 (θ j) :=
  @MathEconLib.Mechanism.revelation_principle_bayesian

/-! ## Definitional checks -/

/-- The pure Nash problem has exactly the unilateral replacement relation. -/
example {I V : Type*} {A : I → Type*} [DecidableEq I] (G : StrategicGame I A V) :
    G.nashProblem =
      { deviation := fun i a b ↦ ∃ s, b = Function.update a i s
        value := G.payoff
        valid := fun _ ↦ True } := rfl

/-- The mixed Nash problem retains its full defining record, including its payoff function. -/
example {I V : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
    [∀ i, MeasurableSpace (A i)] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (G : StrategicGame I A V) :
    G.mixedNashProblem =
      { deviation := fun i σ σ' ↦ (∃ τ, σ' = Function.update σ i τ) ∧
          Integrable (G.payoff i) (Measure.pi (fun j ↦ (σ' j : Measure (A j))))
        value := G.mixedExtension.payoff
        valid := G.MixedPayoffsIntegrable } := rfl

end MathEconLibTest.GameTheory.LawSimulationApi

end
