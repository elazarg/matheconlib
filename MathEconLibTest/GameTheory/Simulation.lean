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

/-- The law-level identity composes without changing the selected certificate. -/
example : (MixtureSimulation.id target.deviation targetLaw
    (fun _ _ ↦ MeasurableSet.of_discrete)).comp lawSimulation
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

end MathEconLibTest.GameTheory.Simulation

/-! ## Equilibrium simulations -/

section EquilibriumSimulation

open MathEconLib.GameTheory

example {S I T J V : Type*} [Preorder V]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    (f : GameSimulation P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) := f.transport h

example {S I T J V : Type*} [LE V]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    (f : GameMorphism P Q) (g : GameComorphism P Q)
    (hmap : g.toFun = f.toFun) (s : S) :
    Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s := f.isEquilibrium_iff g hmap s

example {S I T J V : Type*} [Preorder V] [Add V] [AddRightMono V]
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    (f : GameSimulation P Q) (ε : V) {s : S}
    (h : ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s + ε) :
    ∀ j t, Q.deviation j (f.toFun s) t → Q.value j t ≤ Q.value j (f.toFun s) + ε :=
  f.transport_le_add ε h

end EquilibriumSimulation

/-- Expected-value problems require no measurable structure on the state space. -/
example {S I O V : Type*} [MeasurableSpace O] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (D : I → S → S → Prop) (L : S → Measure O) (u : I → O → V) :
    EquilibriumProblem S I V := .ofExpectedValue D L u

/-- Defining stochastic Nash requires neither measurable actions nor a measurable outcome map. -/
example {I O V : Type*} {A : I → Type*} [DecidableEq I] [MeasurableSpace O]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (G : OutcomeGame I A (ProbabilityMeasure O)) (P : PayoffStructure I O V) :
    EquilibriumProblem (∀ i, A i) I V := G.expectedNashProblem P
