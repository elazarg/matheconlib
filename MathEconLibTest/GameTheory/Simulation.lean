/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium
public import MathEconLib.GameTheory.Strategic.Mixed.Transport
public import MathEconLib.GameTheory.Strategic.Outcome.Transport
public import MathEconLib.ForMathlib.Order.ModuleProd
public import MathEconLib.Probability.FinDist.Measure
public import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Applications and boundaries of equilibrium simulation

A coin action lies outside a compiler's image but is represented by a mixture
of legal source actions. Both ordered and law-level transport apply. The tests
also check composition, reflection, vector averaging, and candidate validity.
-/

@[expose] public noncomputable section

open scoped ENNReal

open MathEconLib.GameTheory MathEconLib.Probability MeasureTheory ProbabilityTheory

namespace MathEconLibTest.GameTheory.Simulation

/-- Two source actions earn zero or one. -/
def source : EquilibriumProblem Bool Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ b ↦ if b then 1 else 0)

/-- The added action earns one half. -/
def target : EquilibriumProblem (Fin 3) Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ q ↦ (q.val : ℝ) / 2)

/-- Compilation includes the two deterministic actions. -/
def compile (b : Bool) : Fin 3 := if b then 2 else 0

lemma target_value_le_one (q : Fin 3) : target.value () q ≤ 1 := by
  change (q.val : ℝ) / 2 ≤ 1
  have hq : (q.val : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ q.isLt
  linarith

/-- The added coin action is bounded by the best source action. -/
def domination : GameSimulation source target where
  toFun := compile
  deviatorMap := id
  valueMap _ := OrderHom.id
  value_le _ b := by cases b <;> norm_num [source, target, compile,
    EquilibriumProblem.ofDeviation]
  deviation_dominated _ _ q _ := ⟨true, trivial, target_value_le_one q⟩
  valid_preserves _ _ := trivial

theorem source_equilibrium : source.IsEquilibrium true := by
  refine ⟨trivial, ?_⟩
  intro _ b _
  cases b <;> norm_num [source, EquilibriumProblem.ofDeviation]

/-- The public simulation theorem establishes equilibrium in the enlarged game. -/
theorem target_equilibrium : target.IsEquilibrium (compile true) :=
  domination.transport source_equilibrium

/-- The chosen compiler cannot lift the new target action exactly. -/
theorem no_exact_morphism : ¬ ∃ f : GameMorphism source target, f.toFun = compile := by
  rintro ⟨f, hf⟩
  obtain ⟨b, _, hb⟩ := f.deviation_lifts () false 1 trivial
  rw [hf] at hb
  cases b <;> norm_num [compile] at hb

/-- Honest compilation maps source deviations, giving independent reflection. -/
def reflection : GameComorphism source target where
  toFun := compile
  deviatorMap := id
  deviation_maps _ _ _ _ := trivial
  value_eq _ b := by cases b <;> norm_num [source, target, compile,
    EquilibriumProblem.ofDeviation]
  valid_reflects _ _ := trivial

theorem equilibrium_iff (b : Bool) : target.IsEquilibrium (compile b) ↔ source.IsEquilibrium b :=
  domination.isEquilibrium_iff reflection rfl b

/-- Coarsening all target states to one state can improve incumbent values. -/
def terminal : EquilibriumProblem Unit Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ _ ↦ 1)

def coarsening : GameSimulation target terminal where
  toFun _ := ()
  deviatorMap := id
  valueMap _ := OrderHom.id
  value_le _ q := target_value_le_one q
  deviation_dominated _ _ _ _ := by
    refine ⟨2, trivial, ?_⟩
    norm_num [terminal, target, EquilibriumProblem.ofDeviation]
  valid_preserves _ _ := trivial

theorem composed_equilibrium : terminal.IsEquilibrium () :=
  (coarsening.comp domination).transport source_equilibrium

/-- Fair randomization between the deterministic outcomes. -/
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

/-- The coin's entire outcome law is reproduced, independently of utilities. -/
def lawSimulation : MixtureSimulation source.deviation target.deviation sourceLaw targetLaw where
  toFun := compile
  deviatorMap := id
  simulate _ _ := targetLaw
  isMarkov_simulate _ _ := inferInstance
  honest_law b := by
    change (weights (compile b)).toMeasure = Measure.dirac b
    cases b <;> simp [compile, weights, pure_law]
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

theorem law_target_equilibrium : target.IsEquilibrium (compile true) :=
  evaluatedSimulation.transport source_equilibrium

/-- The law certificate also transports directly through the averaging theorem. -/
theorem averaging_target_equilibrium : target.IsEquilibrium (compile true) :=
  lawSimulation.transport utility source_evaluation target_evaluation
    (fun _ _ hd _ ↦ hd) (fun _ _ ht ↦ ht) trivial
    (fun i q _ ↦ target_integrable i q) source_equilibrium

/-- A fixed-incumbent law simulation gives a two-law comparison certificate. -/
theorem comparison_bound (q : {q // target.deviation () (compile true) q}) :
    (∫ o, utility () o ∂targetLaw q.val) ≤ ∫ o, utility () o ∂targetLaw (compile true) := by
  apply (lawSimulation.toComparisonMixture () true).preserves_at (utility ()) q
    (target_integrable () (compile true)) (target_integrable () q.val)
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
  toFun a _ := compile (a ())
  deviatorMap := id
  simulate _ _ := Kernel.deterministic (Function.const Unit) Measurable.of_discrete ∘ₖ
    targetOutcome.toKernel
  isMarkov_simulate _ _ := inferInstance
  honest_law a := lawSimulation.honest_law (a ())
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
    (targetOutcome.expectedNashProblem outcomePayoffs).IsEquilibrium (fun _ ↦ compile true) :=
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
  honest_law σ := by exact (mixed_profile_law σ).symm
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

/-- Equal rewards alone do not supply honest observed-law preservation. -/
theorem no_constant_law_simulation : IsEmpty (MixtureSimulation terminal.deviation
    terminal.deviation (Kernel.const Unit (Measure.dirac false))
      (Kernel.const Unit (Measure.dirac true))) := by
  refine ⟨fun f ↦ ?_⟩
  have h := congrArg (fun μ : Measure Bool ↦ μ {true}) (f.honest_law ())
  norm_num [Kernel.const_apply] at h

def invalidTarget : EquilibriumProblem (Fin 3) Unit ℝ := target.refine (fun q ↦ q = 0)

/-- Deviation optimality cannot override an invalid incumbent. -/
theorem invalid_image : ¬ invalidTarget.IsEquilibrium (compile true) := by
  intro h
  have hv := h.valid.2
  norm_num [compile] at hv

/-- An improving deviation still counts even when its target is invalid. -/
theorem invalid_deviation_excludes : ¬ invalidTarget.IsEquilibrium 0 := by
  intro h
  have hd := h.deviation_le () 2 trivial
  norm_num [invalidTarget, target, EquilibriumProblem.refine,
    EquilibriumProblem.ofDeviation] at hd

def localTarget : EquilibriumProblem (Fin 3) Unit ℝ := target.refine (fun q ↦ q = 2)

/-- Local transport works even though the same compiler fails global validity preservation. -/
theorem local_target_equilibrium : localTarget.IsEquilibrium (compile true) := by
  apply lawSimulation.transport (Q := localTarget) utility source_evaluation target_evaluation
    (fun _ _ hd _ ↦ hd) (fun _ _ ht ↦ ht) ?_
    (fun i q _ ↦ target_integrable i q) source_equilibrium
  exact ⟨trivial, rfl⟩

theorem no_global_validity : ¬ ∀ s, source.valid s → localTarget.valid (compile s) := by
  intro h
  have hv := (h false trivial).2
  norm_num [compile] at hv

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

/-! ## Value coordinates and comparison transport -/

/-- Two target players share one source player but use different value coordinates. -/
def vectorRecoding (j : Bool) : ℝ →o ℝ × ℝ where
  toFun x := (if j then 2 * x + 3 else x + 1, x + 7)
  monotone' := by
    intro x y h
    constructor
    · cases j <;> dsimp <;> linarith
    · exact add_le_add_left h 7

def vectorTarget : EquilibriumProblem (Fin 3) Bool (ℝ × ℝ) :=
  .ofDeviation (fun _ _ _ ↦ True) (fun j q ↦ vectorRecoding j (target.value () q))

def recoding : GameSimulation target vectorTarget :=
  .ofExactLifts id (fun _ ↦ ()) vectorRecoding (fun _ _ ↦ rfl)
    (fun _ _ t _ ↦ ⟨t, trivial, rfl⟩) (fun _ _ ↦ trivial)

/-- Reflection works across value spaces even when the compiler omits a target state. -/
theorem cross_value_equilibrium_iff (b : Bool) :
    vectorTarget.IsEquilibrium (compile b) ↔ source.IsEquilibrium b := by
  apply (recoding.comp domination).isEquilibrium_iff_of_deviation_comparisons
    (fun _ ↦ false) (fun _ ↦ trivial)
  intro i b' _
  refine ⟨compile b', trivial, fun hle ↦ ?_⟩
  have hscalar := (add_le_add_iff_right (7 : ℝ)).mp hle.2
  exact (reflection.value_eq () b').ge.trans (hscalar.trans (reflection.value_eq () b).le)

def firstCoordinate : (ℝ × ℝ) →o ℝ :=
  ⟨fun v ↦ v.1 + 11, fun _ _ h ↦ add_le_add_left h.1 11⟩

def finalTarget : EquilibriumProblem (Fin 3) Unit ℝ :=
  .ofDeviation (fun _ _ _ ↦ True) (fun _ q ↦ firstCoordinate (vectorTarget.value true q))

def projecting : GameSimulation vectorTarget finalTarget :=
  .ofExactLifts id (fun _ ↦ true) (fun _ ↦ firstCoordinate) (fun _ _ ↦ rfl)
    (fun _ _ t _ ↦ ⟨t, trivial, rfl⟩) (fun _ _ ↦ trivial)

/-- Nontrivial value maps compose across different value spaces and player sets. -/
theorem recoded_equilibrium : finalTarget.IsEquilibrium (compile true) :=
  (projecting.comp (recoding.comp domination)).transport source_equilibrium

def affineRecoding : ℝ →o ℝ :=
  ⟨fun x ↦ 3 * x + 7, fun _ _ h ↦ by linarith⟩

def rescaled : EquilibriumProblem Bool Unit ℝ := source.mapValues (fun _ ↦ affineRecoding)

def rescaling : GameSimulation source rescaled :=
  .ofExactLifts id id (fun _ ↦ affineRecoding) (fun _ _ ↦ rfl)
    (fun _ _ t ht ↦ ⟨t, ht, rfl⟩) (fun _ ht ↦ ht)

/-- The compatibility premise scales errors by the affine slope, not by the offset. -/
theorem rescaled_error {s : Bool} (ε : ℝ)
    (h : ∀ i b, source.deviation i s b → source.value i b ≤ source.value i s + ε) :
    ∀ j b, rescaled.deviation j s b → rescaled.value j b ≤ rescaled.value j s + 3 * ε := by
  apply rescaling.transport_le_add (fun _ ↦ ε) (fun _ ↦ 3 * ε) _ h
  intro j
  change 3 * (source.value () s + ε) + 7 ≤ (3 * source.value () s + 7) + 3 * ε
  linarith

theorem rescaled_approximate_false :
    ∀ j b, rescaled.deviation j false b → rescaled.value j b ≤ rescaled.value j false + 3 := by
  simpa only [mul_one] using rescaled_error (s := false) 1
    (by intro i b _; cases b <;> norm_num [source, EquilibriumProblem.ofDeviation])

theorem same_error_fails : ¬ ∀ j b, rescaled.deviation j false b →
    rescaled.value j b ≤ rescaled.value j false + 1 := by
  intro h
  have := h () true trivial
  change 3 * 1 + 7 ≤ (3 * 0 + 7 : ℝ) + 1 at this
  norm_num at this

/-- A monotone collapse creates an equilibrium at a previously suboptimal state. -/
theorem collapsed_equilibrium :
    (source.mapValues (fun _ _ ↦ (0 : ℝ))).IsEquilibrium false :=
  ⟨trivial, fun _ _ _ ↦ le_rfl⟩

theorem source_not_equilibrium_false : ¬ source.IsEquilibrium false := by
  intro h
  have := h.deviation_le () true trivial
  norm_num [source, EquilibriumProblem.ofDeviation] at this

/-- The second coordinate is fixed during every admitted deviation. -/
def contextualSource : EquilibriumProblem (Bool × Bool) Unit ℝ :=
  .ofDeviation (fun _ s t ↦ t.2 = s.2) (fun _ s ↦ if s.1 then 1 else 0)

def contextualTarget : EquilibriumProblem (Bool × Bool) Unit ℝ :=
  .ofDeviation contextualSource.deviation
    (fun i s ↦ contextualSource.value i s + if s.2 then 10 else 0)

/-- Offsets constant along legal deviations need no global function of source values. -/
theorem contextual_transport {s : Bool × Bool} (h : contextualSource.IsEquilibrium s) :
    contextualTarget.IsEquilibrium s := by
  apply h.of_deviation_comparisons id trivial
  intro i t ht
  refine ⟨t, ht, fun hle ↦ ?_⟩
  change t.2 = s.2 at ht
  change contextualSource.value i t + _ ≤ contextualSource.value i s + _
  rw [ht]
  exact add_le_add_left hle _

example : contextualTarget.IsEquilibrium (true, false) :=
  contextual_transport ⟨trivial, by
    intro i t _
    change (if t.1 then (1 : ℝ) else 0) ≤ 1
    split <;> norm_num⟩

theorem no_global_value_map : ¬ ∃ φ : ℝ → ℝ,
    ∀ s, contextualTarget.value () s = φ (contextualSource.value () s) := by
  rintro ⟨φ, hφ⟩
  have h0 := hφ (true, false)
  have h1 := hφ (true, true)
  norm_num [contextualSource, contextualTarget, EquilibriumProblem.ofDeviation] at h0 h1
  linarith

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

end MathEconLibTest.GameTheory.Simulation

/-! ## Equilibrium simulations -/

section EquilibriumSimulation

example {S I T J V W : Type*} [Preorder V] [Preorder W]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) := f.transport h

example {S I T J V : Type*} [LE V]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    (f : GameMorphism P Q) (g : GameComorphism P Q)
    (hmap : g.toFun = f.toFun) (s : S) :
    Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s := f.isEquilibrium_iff g hmap s

example {S I T J V W : Type*} [Preorder V] [Preorder W] [Add V] [Add W] [AddRightMono W]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
    (f : GameSimulation P Q) (ε : I → V) (δ : J → W) {s : S}
    (herror : ∀ j, f.valueMap j (P.value (f.deviatorMap j) s + ε (f.deviatorMap j)) ≤
      f.valueMap j (P.value (f.deviatorMap j) s) + δ j)
    (h : ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s + ε i) :
    ∀ j t, Q.deviation j (f.toFun s) t → Q.value j t ≤ Q.value j (f.toFun s) + δ j :=
  f.transport_le_add ε δ herror h

end EquilibriumSimulation

/-- The comparison core requires no order laws and permits different value spaces. -/
example {S I T J V W : Type*} [LE V] [LE W]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W} {s : S} {t : T}
    (h : P.IsEquilibrium s) (g : J → I) (hvalid : Q.valid t)
    (hdev : ∀ j t', Q.deviation j t t' → ∃ s', P.deviation (g j) s s' ∧
      (P.value (g j) s' ≤ P.value (g j) s → Q.value j t' ≤ Q.value j t)) :
    Q.IsEquilibrium t := h.of_deviation_comparisons g hvalid hdev

/-- Standard order embeddings preserve and reflect equilibrium without being onto. -/
example {S I V W : Type*} [LE V] [LE W] (P : EquilibriumProblem S I V)
    (φ : I → V ↪o W) (s : S) :
    (P.mapValues (fun i ↦ φ i)).IsEquilibrium s ↔ P.IsEquilibrium s :=
  P.isEquilibrium_mapValues_iff _ (fun i _ _ ↦ (φ i).map_rel_iff) s

/-- Expected-value problems require no measurable structure on the state space. -/
example {S I O V : Type*} [MeasurableSpace O] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (D : I → S → S → Prop) (L : S → Measure O) (u : I → O → V) :
    EquilibriumProblem S I V := .ofExpectedValue D L u

/-- Affine outcome recoding needs probability laws, but no global utility integrability. -/
example {S I O : Type*} [MeasurableSpace O] (D : I → S → S → Prop) (L : S → Measure O)
    [∀ s, IsProbabilityMeasure (L s)] (u : I → O → ℝ) (a c : I → ℝ)
    (ha : ∀ i, 0 < a i) (s : S) :
    (EquilibriumProblem.ofExpectedValue D L (fun i o ↦ a i * u i o + c i)).IsEquilibrium s ↔
      (EquilibriumProblem.ofExpectedValue D L u).IsEquilibrium s :=
  EquilibriumProblem.isEquilibrium_ofExpectedValue_affine_iff D L u a c ha s

/-- At undefined expectations, affine invariance of equilibria is not equality of value records. -/
example {O : Type*} [MeasurableSpace O] (μ : ProbabilityMeasure O) (u : O → ℝ)
    (hu : ¬ Integrable u μ) :
    ((EquilibriumProblem.ofExpectedValue (fun (_ : Unit) (_ _ : Unit) ↦ True)
      (fun _ ↦ (μ : Measure O)) (fun _ ↦ u)).mapValues (fun _ x ↦ x + 1)).value () () ≠
      (EquilibriumProblem.ofExpectedValue (fun (_ : Unit) (_ _ : Unit) ↦ True)
        (fun _ ↦ (μ : Measure O)) (fun _ o ↦ u o + 1)).value () () := by
  change (∫ o, u o ∂μ) + 1 ≠ ∫ o, u o + 1 ∂μ
  rw [integral_undef hu, integral_undef (fun h ↦ hu (integrable_add_const_iff.mp h))]
  norm_num

/-- Defining stochastic Nash requires neither measurable actions nor a measurable outcome map. -/
example {I O V : Type*} {A : I → Type*} [DecidableEq I] [MeasurableSpace O]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (G : OutcomeGame I A (ProbabilityMeasure O)) (P : PayoffStructure I O V) :
    EquilibriumProblem (∀ i, A i) I V := G.expectedNashProblem P

/-- Reindexing bounded utilities needs no measurable or topological structure. -/
example {I J O V : Type*} [Bornology V] (P : PayoffStructure I O V) [P.Bounded] (f : J → I) :
    (P.reindex f).Bounded := inferInstance

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
