/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.Simulation
public import MathEconLib.GameTheory.Equilibrium
public import MathEconLib.GameTheory.Strategic.Mixed.Transport
public import MathEconLib.GameTheory.Strategic.Outcome.Transport
public import MathEconLib.ForMathlib.Order.ModuleProd
public import MathEconLib.Probability.FinDist.Measure
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Law simulation, averaging, and expected-utility transport

The added action of `MathEconLibTest.GameTheory.Simulation` is represented by a fair mixture of
the two source actions. Law simulation, ordered averaging, and the real-valued simulation they
induce all transport the source equilibrium. The tests also check stochastic outcome games, the
pure-to-mixed embedding with vector payoffs, identity and composition of mixture witnesses,
candidate validity and integrability restrictions, and the boundaries: a vector mean need not be
dominated by one source deviation, and recoding expected values differs from recoding utilities.
-/

@[expose] public noncomputable section

open scoped ENNReal

open MathEconLib.GameTheory MathEconLib.Probability MeasureTheory ProbabilityTheory
open MathEconLibTest.GameTheory.Simulation

namespace MathEconLibTest.GameTheory.LawSimulation

def fair : FinDist Bool :=
  FinDist.mixture ⟨1 / 2, by constructor <;> norm_num⟩
    (FinDist.pure false) (FinDist.pure true)

def weights (q : Fin 3) : FinDist Bool :=
  if q = 1 then fair else FinDist.pure (decide (q = 2))

private lemma pure_law (b : Bool) : (FinDist.pure b).toMeasure = Measure.dirac b := by
  have hp : (FinDist.pure b).toPMF = PMF.pure b := by
    ext x
    change ENNReal.ofReal (if b = x then 1 else 0) = (PMF.pure b) x
    rw [PMF.pure_apply]
    by_cases h : b = x <;> simp_all [eq_comm]
  rw [FinDist.toMeasure, hp, PMF.toMeasure_pure]

def sourceLaw : Kernel Bool Bool := Kernel.id

instance : IsMarkovKernel sourceLaw := inferInstanceAs (IsMarkovKernel Kernel.id)

def targetLaw : Kernel (Fin 3) Bool where
  toFun q := (weights q).toMeasure
  measurable' := Measurable.of_discrete

instance : IsMarkovKernel targetLaw := ⟨fun q ↦
  show IsProbabilityMeasure (weights q).toMeasure from inferInstance⟩

/-- The added action's entire outcome law is reproduced, independently of utilities. -/
def lawSimulation : MixtureSimulation source.deviation target.deviation sourceLaw targetLaw where
  toFun := inclusion
  deviatorMap := id
  simulate _ _ := targetLaw
  isMarkov_simulate _ _ := inferInstance
  incumbent_law_eq b := by
    change (weights (inclusion b)).toMeasure = Measure.dirac b
    cases b <;> simp [inclusion, weights, pure_law]
  deviation_ae _ _ _ _ := ae_of_all _ fun _ ↦ trivial
  deviation_law _ _ _ _ := by simp [sourceLaw]

def utility (_ : Unit) (b : Bool) : ℝ := if b then 1 else 0

lemma source_evaluation (i : Unit) (b : Bool) :
    source.value i b = ∫ o, utility i o ∂sourceLaw b := by
  simp [sourceLaw, Kernel.id_apply, source, utility, EquilibriumProblem.ofDeviation]

lemma target_evaluation (i : Unit) (q : Fin 3) :
    target.value i q = ∫ o, utility i o ∂targetLaw q := by
  change (q.val : ℝ) / 2 = ∫ o, utility i o ∂(weights q).toMeasure
  rw [← FinDist.expect_eq_integral]
  fin_cases q <;> norm_num [weights, fair, FinDist.expect_mixture, FinDist.expect_pure, utility]

lemma target_integrable (i : Unit) (q : Fin 3) : Integrable (utility i) (targetLaw q) :=
  (weights q).integrable_toMeasure _

/-- The mean-bound witness is legal and has a genuine finite expected utility. -/
example : ∃ b, source.deviation () false b ∧ Integrable (utility ()) (sourceLaw b) ∧
    (∫ o, utility () o ∂targetLaw 1) ≤ ∫ o, utility () o ∂sourceLaw b :=
  lawSimulation.exists_source_deviation_ge utility trivial (target_integrable () 1)

/-- The general law-to-utility relationship yields a second simulation certificate. -/
def evaluatedSimulation : GameSimulation source target :=
  lawSimulation.toSimulation utility source_evaluation target_evaluation
    (fun _ _ _ hd _ ↦ hd) (fun _ _ _ ht ↦ ht)
    (fun _ _ ↦ trivial) (fun i _ q _ ↦ target_integrable i q)

theorem law_target_equilibrium : target.IsEquilibrium (inclusion true) :=
  evaluatedSimulation.transport source_equilibrium

/-- The law certificate also transports directly through the averaging theorem. -/
theorem averaging_target_equilibrium : target.IsEquilibrium (inclusion true) :=
  lawSimulation.transport utility source_evaluation target_evaluation
    (fun _ _ hd _ ↦ hd) (fun _ _ ht ↦ ht) trivial
    (fun i q _ ↦ target_integrable i q) source_equilibrium

/-- A fixed-incumbent law simulation gives a two-law comparison certificate. -/
theorem comparison_bound (q : {q // target.deviation () (inclusion true) q}) :
    (∫ o, utility () o ∂targetLaw q.val) ≤ ∫ o, utility () o ∂targetLaw (inclusion true) := by
  apply (lawSimulation.toComparisonMixture () true).preserves_at (utility ()) q
    (target_integrable () (inclusion true)) (target_integrable () q.val)
  apply ae_of_all
  intro b
  change (∫ o, utility () o ∂sourceLaw b) ≤ ∫ o, utility () o ∂sourceLaw true
  rw [← source_evaluation, ← source_evaluation]
  exact source_equilibrium.deviation_le () b trivial

/-- Prescribed laws may vary across the source comparisons. The target's fair
prescribed law is not the prescribed law of either source comparison. -/
def varyingComparison : ComparisonMixture sourceLaw (Kernel.const Bool (sourceLaw false))
    (Kernel.const Unit (targetLaw 1)) (Kernel.const Unit (sourceLaw false)) where
  mixing := Kernel.const Unit (targetLaw 1)
  isMarkov_mixing := inferInstance
  prescribed_eq := Kernel.id_comp _
  alternative_eq := Kernel.const_comp' _ _

theorem varying_comparison_bound :
    (∫ o, utility () o ∂sourceLaw false) ≤ ∫ o, utility () o ∂targetLaw 1 := by
  apply varyingComparison.preserves_at (utility ()) ()
    (target_integrable () 1) (Integrable.of_finite)
  apply ae_of_all
  intro b
  change (∫ o, utility () o ∂sourceLaw false) ≤ ∫ o, utility () o ∂sourceLaw b
  rw [← source_evaluation, ← source_evaluation]
  cases b <;> norm_num [source, EquilibriumProblem.ofDeviation]

theorem no_prescribed_source (b : Bool) : sourceLaw b ≠ targetLaw 1 := by
  intro h
  have he := congrArg (fun μ ↦ ∫ o, utility () o ∂μ) h
  rw [← source_evaluation, ← target_evaluation] at he
  cases b <;> norm_num [source, target, EquilibriumProblem.ofDeviation] at he

/-- The same law certificate serves stochastic outcome games directly. -/
def sourceOutcome : OutcomeGame Unit (fun _ ↦ Bool) (ProbabilityMeasure Bool) where
  outcome a := ⟨sourceLaw (a ()), inferInstance⟩

instance : sourceOutcome.Measurable := ⟨Measurable.of_discrete⟩

def targetOutcome : OutcomeGame Unit (fun _ ↦ Fin 3) (ProbabilityMeasure Bool) where
  outcome a := ⟨targetLaw (a ()), inferInstance⟩

instance : targetOutcome.Measurable := ⟨Measurable.of_discrete⟩

def outcomePayoffs : PayoffStructure Unit Bool ℝ := ⟨utility⟩

private lemma unit_unilateral {A : Type*} (a b : Unit → A) :
    IsUnilateralDeviation () a b :=
  (isUnilateralDeviation_iff () a b).mpr fun j hj ↦ (hj (Subsingleton.elim j ())).elim

private lemma sourceOutcome_kernel : sourceOutcome.toKernel =
    Kernel.deterministic (fun a : Unit → Bool ↦ a ()) (measurable_pi_apply ()) := by
  apply Kernel.ext
  intro a
  rfl

def outcomeSimulation : MixtureSimulation IsUnilateralDeviation IsUnilateralDeviation
    sourceOutcome.toKernel targetOutcome.toKernel where
  toFun a _ := inclusion (a ())
  deviatorMap := id
  simulate _ _ := Kernel.deterministic (Function.const Unit) Measurable.of_discrete ∘ₖ
    targetOutcome.toKernel
  isMarkov_simulate _ _ := inferInstance
  incumbent_law_eq a := lawSimulation.incumbent_law_eq (a ())
  deviation_ae j a _ _ := by
    cases j
    exact ae_of_all _ (unit_unilateral a)
  deviation_law _ _ t _ := by
    rw [sourceOutcome_kernel, ← Kernel.comp_assoc, Kernel.deterministic_comp_deterministic]
    change (Kernel.id ∘ₖ targetOutcome.toKernel) t = targetOutcome.toKernel t
    rw [Kernel.id_comp]

theorem source_outcome_equilibrium :
    (sourceOutcome.expectedNashProblem outcomePayoffs).IsEquilibrium (fun _ ↦ true) := by
  refine ⟨fun _ ↦ Integrable.of_finite, ?_⟩
  intro i a _
  change (∫ o, utility i o ∂sourceLaw (a ())) ≤ ∫ o, utility i o ∂sourceLaw true
  rw [← source_evaluation, ← source_evaluation]
  exact source_equilibrium.deviation_le i (a ()) trivial

/-- Outcome laws, payoff evaluation, and admissibility are supplied by the adapter. -/
theorem target_outcome_equilibrium :
    (targetOutcome.expectedNashProblem outcomePayoffs).IsEquilibrium (fun _ ↦ inclusion true) :=
  outcomeSimulation.transport_expectedNash outcomePayoffs source_outcome_equilibrium

/-- The two objectives have a common maximizing action. -/
def vectorGame : StrategicGame Unit (fun _ ↦ Bool) (ℝ × ℝ) where
  payoff _ a := if a () then (1, 2) else (0, 0)

theorem vector_pure : vectorGame.IsNash (fun _ ↦ true) := by
  rw [StrategicGame.isNash_iff]
  intro i b
  cases i
  cases b <;> norm_num [vectorGame]

/-- Apply the general Dirac theorem to actual vector-valued mixed Nash. -/
theorem vector_mixed : vectorGame.IsMixedNash (fun _ ↦ diracProba true) :=
  vector_pure.isMixedNash_dirac

/-- An extra action component leaves the actual randomized outcome unchanged. -/
def redundantMixedOutcome : OutcomeGame Unit (fun _ ↦ ProbabilityMeasure Bool × Bool)
    (ProbabilityMeasure (Unit → Bool)) where
  outcome a := ProbabilityMeasure.pi (fun i ↦ (a i).1)

instance : redundantMixedOutcome.Measurable where
  measurable_outcome := ProbabilityMeasure.measurable_pi.comp <|
    Measurable.of_eval fun i ↦ (measurable_pi_apply i).fst

private lemma mixed_profile_law (σ : StrategicGame.MixedStrategy (fun _ : Unit ↦ Bool)) :
    vectorGame.outcomeGame.mixed.toKernel σ =
      (ProbabilityMeasure.pi σ : Measure (Unit → Bool)) := by
  simp [OutcomeGame.mixed, StrategicGame.outcomeGame]

def redundantMixedSimulation : MixtureSimulation IsUnilateralDeviation IsUnilateralDeviation
    vectorGame.outcomeGame.mixed.toKernel redundantMixedOutcome.toKernel where
  toFun σ i := (σ i, false)
  deviatorMap := id
  simulate _ _ := Kernel.deterministic (fun a i ↦ (a i).1)
    (Measurable.of_eval fun i ↦ (measurable_pi_apply i).fst)
  isMarkov_simulate _ _ := inferInstance
  incumbent_law_eq σ := by exact (mixed_profile_law σ).symm
  deviation_ae i σ _ _ := by
    cases i
    exact ae_of_all _ (unit_unilateral σ)
  deviation_law _ _ t _ := by
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, mixed_profile_law]
    rfl

/-- Native mixed Nash transports through a law simulation with a redundant action. -/
theorem redundant_mixed_equilibrium :
    (redundantMixedOutcome.expectedNashProblem vectorGame.payoffStructure).IsEquilibrium
      (fun _ ↦ (diracProba true, false)) :=
  redundantMixedSimulation.transport_isMixedNash vector_mixed

/-- The law-level identity composes without changing the selected certificate. -/
example : (MixtureSimulation.id target.deviation targetLaw
    (fun _ _ ↦ MeasurableSet.of_discrete)).comp lawSimulation
      (fun _ _ ↦ MeasurableSet.of_discrete) = lawSimulation := by simp

example : (MixtureSimulation.idOfMeasurableSingleton target.deviation targetLaw).comp
    lawSimulation (fun _ _ ↦ MeasurableSet.of_discrete) = lawSimulation := by simp

example : lawSimulation.comp (MixtureSimulation.idOfMeasurableSingleton source.deviation sourceLaw)
    (fun _ _ ↦ MeasurableSet.of_discrete) = lawSimulation := by simp

/-- Arbitrary deviation predicates on the real line admit identity simulation. -/
example (D : Unit → ℝ → ℝ → Prop) : MixtureSimulation D D Kernel.id Kernel.id :=
  .idOfMeasurableSingleton D Kernel.id

/-- Bare unilateral deviations admit law identities with arbitrary measurable
action spaces and countably many players, without an integrability-set premise. -/
example {I : Type*} {A : I → Type*} [Countable I] [DecidableEq I]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)] :
    MixtureSimulation (IsUnilateralDeviation (A := A)) IsUnilateralDeviation Kernel.id Kernel.id :=
  .id _ _ measurableSet_isUnilateralDeviation

/-- A finite vector payoff whose mean has no dominating support point. -/
def vectorUtility (b : Bool) : ℝ × ℝ := if b then (1, 0) else (0, 1)

lemma vector_integral : (∫ b, vectorUtility b ∂fair.toMeasure) = (1 / 2, 1 / 2) := by
  rw [← FinDist.expect_eq_integral]
  norm_num [fair, vectorUtility, FinDist.expect_mixture, FinDist.expect_pure]

/-- An integrable vector mean need not have a componentwise dominating support point. -/
theorem no_vector_mean_witness :
    ¬ ∃ b : Bool, (∫ b, vectorUtility b ∂fair.toMeasure) ≤ vectorUtility b := by
  rw [vector_integral]
  rintro ⟨b, hb⟩
  cases b <;> norm_num [vectorUtility] at hb

/-- Equal rewards alone do not give equal incumbent outcome laws. -/
theorem no_constant_law_simulation : IsEmpty (MixtureSimulation terminal.deviation
    terminal.deviation (Kernel.const Unit (Measure.dirac false))
      (Kernel.const Unit (Measure.dirac true))) := by
  refine ⟨fun f ↦ ?_⟩
  have h := congrArg (fun μ : Measure Bool ↦ μ {true}) (f.incumbent_law_eq ())
  norm_num [Kernel.const_apply] at h

def invalidTarget : EquilibriumProblem (Fin 3) Unit ℝ := target.refine (fun q ↦ q = 0)

/-- Deviation optimality cannot override an invalid incumbent. -/
theorem invalid_image : ¬ invalidTarget.IsEquilibrium (inclusion true) := by
  intro h
  have hv := h.valid.2
  norm_num [inclusion] at hv

/-- An improving deviation still counts even when its target is invalid. -/
theorem invalid_deviation_excludes : ¬ invalidTarget.IsEquilibrium 0 := by
  intro h
  have hd := h.deviation_le () 2 trivial
  norm_num [invalidTarget, target, EquilibriumProblem.refine,
    EquilibriumProblem.ofDeviation] at hd

def localTarget : EquilibriumProblem (Fin 3) Unit ℝ := target.refine (fun q ↦ q = 2)

/-- Local transport works even though the same inclusion fails global validity preservation. -/
theorem local_target_equilibrium : localTarget.IsEquilibrium (inclusion true) := by
  apply lawSimulation.transport (Q := localTarget) utility source_evaluation target_evaluation
    (fun _ _ hd _ ↦ hd) (fun _ _ ht ↦ ht) ?_
    (fun i q _ ↦ target_integrable i q) source_equilibrium
  exact ⟨trivial, rfl⟩

theorem no_global_validity : ¬ ∀ s, source.valid s → localTarget.valid (inclusion s) := by
  intro h
  have hv := (h false trivial).2
  norm_num [inclusion] at hv

/-- General observation kernels may include laws with nonintegrable utility. -/
def partialLaw : Kernel Bool Unit where
  toFun b := if b then (⊤ : ℝ≥0∞) • Measure.dirac () else Measure.dirac ()
  measurable' := Measurable.of_discrete

lemma partial_integrable (b : Bool) :
    Integrable (fun _ : Unit ↦ (1 : ℝ)) (partialLaw b) ↔ b = false := by
  cases b <;> simp [partialLaw, integrable_const_iff, isFiniteMeasure_iff]

def integrableSource : EquilibriumProblem Bool Unit ℝ :=
  .ofExpectedValue (fun _ _ b ↦ b = false) partialLaw (fun _ _ ↦ 1)

def integrableTarget : EquilibriumProblem Bool Unit ℝ :=
  .ofExpectedValue (fun _ _ _ ↦ True) partialLaw (fun _ _ ↦ 1)

theorem integrable_source_equilibrium : integrableSource.IsEquilibrium false := by
  refine ⟨fun _ ↦ (partial_integrable false).mpr rfl, ?_⟩
  intro _ b hb
  obtain rfl := hb.1
  exact le_rfl

/-- Conditional source admissibility and admitted-target integrability suffice,
although the bare simulation relation also covers the nonintegrable state. -/
theorem transport_with_integrability_restriction : integrableTarget.IsEquilibrium false :=
  (MixtureSimulation.idOfMeasurableSingleton
    (fun (_ : Unit) (_ _ : Bool) ↦ True) partialLaw).transport
    (P := integrableSource) (Q := integrableTarget) (fun _ _ ↦ 1)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ b _ hi ↦ ⟨(partial_integrable b).mp hi, hi⟩) (fun _ _ ht ↦ ht.1)
    integrable_source_equilibrium.valid (fun _ _ ht ↦ ht.2) integrable_source_equilibrium

theorem bare_source_deviation_not_admissible : ¬ integrableSource.deviation () false true := by
  intro h
  exact Bool.noConfusion h.1

theorem not_all_bare_deviations_integrable :
    ¬ ∀ b, Integrable (fun _ : Unit ↦ (1 : ℝ)) (partialLaw b) := by
  intro h
  simpa using (partial_integrable true).mp (h true)


/-- A monotone collapse creates an equilibrium at a previously suboptimal state. -/
theorem collapsed_equilibrium :
    (source.mapValues (fun _ _ ↦ (0 : ℝ))).IsEquilibrium false :=
  ⟨trivial, fun _ _ _ ↦ le_rfl⟩

theorem source_not_equilibrium_false : ¬ source.IsEquilibrium false := by
  intro h
  have := h.deviation_le () true trivial
  norm_num [source, EquilibriumProblem.ofDeviation] at this


def fairEvaluation (u : Bool → ℝ) : EquilibriumProblem Unit Unit ℝ :=
  .ofExpectedValue (fun _ _ _ ↦ True) (fun _ ↦ fair.toMeasure) (fun _ ↦ u)

/-- Recoding the expected payoff differs from recoding outcome utilities before averaging. -/
theorem nonlinear_before_after :
    ((fairEvaluation (fun b ↦ if b then 2 else 0)).mapValues (fun _ x ↦ x ^ 3)).value () () ≠
      (fairEvaluation (fun b ↦ (if b then 2 else 0) ^ 3)).value () () := by
  change (∫ b, (if b then (2 : ℝ) else 0) ∂fair.toMeasure) ^ 3 ≠
    ∫ b, (if b then (2 : ℝ) else 0) ^ 3 ∂fair.toMeasure
  rw [← FinDist.expect_eq_integral, ← FinDist.expect_eq_integral]
  norm_num [fair, FinDist.expect_mixture, FinDist.expect_pure]

end MathEconLibTest.GameTheory.LawSimulation
