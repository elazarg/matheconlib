/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium
public import MathEconLib.GameTheory.Strategic.Mixed.Transport
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
  lawSimulation.toSimulation utility source_evaluation target_evaluation rfl rfl
    (fun _ _ ↦ trivial) (fun i _ q _ ↦ target_integrable i q)

theorem law_target_equilibrium : target.IsEquilibrium (compile true) :=
  evaluatedSimulation.transport source_equilibrium

/-- The law certificate also transports directly through the averaging theorem. -/
theorem averaging_target_equilibrium : target.IsEquilibrium (compile true) :=
  lawSimulation.transport utility source_evaluation target_evaluation rfl rfl
    (fun _ _ ↦ trivial) (fun i _ q _ ↦ target_integrable i q) source_equilibrium

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

/-- Vector averaging need not have a componentwise dominating support point. -/
theorem no_vector_mean_witness :
    ¬ ∃ b : Bool, ((1 / 2 : ℝ), (1 / 2 : ℝ)) ≤ (if b then (1, 0) else (0, 1)) := by
  rintro ⟨b, hb⟩
  cases b <;> norm_num at hb

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

end MathEconLibTest.GameTheory.Simulation
