/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Mixed
public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Infinite gains outside finite-integrable deviations

A Boolean decision accepts an exponential payoff against a geometric opponent.
Every admitted deviation has finite payoff zero, but accepting with positive
probability has infinite nonnegative integral. The finite-integrable and
nonnegative-extended comparison conventions therefore give different verdicts.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.GameTheory.InfiniteGain

open MeasureTheory MathEconLib.GameTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- Only the first player controls the Boolean decision to accept the gamble. -/
abbrev Action : Bool → Type
  | false => Bool
  | true => ℕ

instance actionMeasurableSpace : ∀ i, MeasurableSpace (Action i)
  | false => ⊤
  | true => ⊤

instance actionMeasurableSingleton (i : Bool) : MeasurableSingletonClass (Action i) := by
  cases i <;> exact ⟨fun _ => trivial⟩

instance actionCountable (i : Bool) : Countable (Action i) := by
  cases i
  · exact inferInstanceAs (Countable Bool)
  · exact inferInstanceAs (Countable ℕ)

def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem half_ne_zero : half ≠ 0 := by
  intro equal
  have real_equal : (half : ℝ) = 0 := congrArg Subtype.val equal
  norm_num [half] at real_equal

def geometric : ProbabilityMeasure ℕ := ⟨geometricMeasure half, inferInstance⟩

def falseAction : ProbabilityMeasure Bool := ⟨Measure.dirac false, inferInstance⟩
def trueAction : ProbabilityMeasure Bool := ⟨Measure.dirac true, inferInstance⟩

def incumbent : StrategicGame.MixedStrategy Action
  | false => falseAction
  | true => geometric

def profileLaw (strategy : StrategicGame.MixedStrategy Action) : Measure (∀ i, Action i) :=
  Measure.pi fun i => (strategy i : Measure (Action i))

def lawAt (replacement : ProbabilityMeasure Bool) : Measure (∀ i, Action i) :=
  profileLaw (Function.update incumbent false replacement)

def gain (n : ℕ) : ℝ := 2 ^ (n + 1)

def game : StrategicGame Bool Action ℝ where
  payoff
    | false, action => if action false then gain (action true) else 0
    | true, _ => 0

def point (own : Bool) (n : ℕ) : ∀ i, Action i
  | false => own
  | true => n

theorem point_true_injective : Function.Injective (point true) := by
  intro n m equal
  exact congrFun equal true

theorem gain_nonnegative (action : ∀ i, Action i) : 0 ≤ game.payoff false action := by
  change 0 ≤ if action false then gain (action true) else 0
  split
  · unfold gain
    positivity
  · exact le_rfl

theorem true_atom (replacement : ProbabilityMeasure Bool) (n : ℕ) :
    lawAt replacement {point true n} =
      (replacement : Measure Bool) {true} * geometricMeasure half {n} := by
  simp [lawAt, profileLaw, Measure.pi_singleton,
    incumbent, point, geometric, mul_comm]

/-- Each exponential payoff cancels its geometric atom exactly. -/
theorem weighted_gain (n : ℕ) :
    ENNReal.ofReal (gain n) * geometricMeasure half {n} = 1 := by
  rw [geometricMeasure_singleton half_ne_zero]
  have weight : (1 - (half : ℝ)) ^ n * (half : ℝ) = (1 : ℝ) / 2 / 2 ^ n := by
    norm_num [half, div_pow]
    ring
  rw [weight, ← ENNReal.ofReal_mul (by unfold gain; positivity)]
  have product : gain n * ((1 : ℝ) / 2 / 2 ^ n) = 1 := by
    unfold gain
    rw [pow_succ]
    field_simp
  rw [product, ENNReal.ofReal_one]

theorem payoff_atom (replacement : ProbabilityMeasure Bool) (n : ℕ) :
    ENNReal.ofReal (game.payoff false (point true n)) *
      lawAt replacement {point true n} = (replacement : Measure Bool) {true} := by
  rw [true_atom]
  change ENNReal.ofReal (gain n) *
    ((replacement : Measure Bool) {true} * geometricMeasure half {n}) = _
  calc
    _ = (replacement : Measure Bool) {true} *
        (ENNReal.ofReal (gain n) * geometricMeasure half {n}) := by ac_rfl
    _ = _ := by rw [weighted_gain, mul_one]

/-- Any positive probability of accepting the gamble gives infinite expected
nonnegative gain, under the actual independent product law. -/
theorem positive_gain_infinite (replacement : ProbabilityMeasure Bool)
    (positive_mass : (replacement : Measure Bool) {true} ≠ 0) :
    (∫⁻ action, ENNReal.ofReal (game.payoff false action) ∂lawAt replacement) = ⊤ := by
  have lower := ENNReal.tsum_comp_le_tsum_of_injective point_true_injective
    (fun action => ENNReal.ofReal (game.payoff false action) * lawAt replacement {action})
  simp only [payoff_atom] at lower
  rw [ENNReal.tsum_const_eq_top_of_ne_zero positive_mass] at lower
  rw [lintegral_countable']
  exact top_unique lower

theorem positive_mass_not_integrable (replacement : ProbabilityMeasure Bool)
    (positive_mass : (replacement : Measure Bool) {true} ≠ 0) :
    ¬ Integrable (game.payoff false) (lawAt replacement) := by
  intro integrable
  have finite := integrable.lintegral_lt_top
  rw [positive_gain_infinite replacement positive_mass] at finite
  exact lt_irrefl _ finite

/-- With zero probability of accepting, the payoff is zero almost surely. -/
theorem zero_mass_payoff_zero (replacement : ProbabilityMeasure Bool)
    (zero_mass : (replacement : Measure Bool) {true} = 0) :
    game.payoff false =ᵐ[lawAt replacement] fun _ => 0 := by
  apply ae_iff_of_countable.mpr
  intro action supported
  cases own : action false
  · simp [game, own]
  · exfalso
    apply supported
    simp [lawAt, profileLaw, Measure.pi_singleton,
      incumbent, geometric, own, zero_mass]

theorem integrable_deviation_payoff_zero (replacement : ProbabilityMeasure Bool)
    (integrable : Integrable (game.payoff false) (lawAt replacement)) :
    (∫ action, game.payoff false action ∂lawAt replacement) = 0 := by
  have zero_mass : (replacement : Measure Bool) {true} = 0 := by
    by_contra positive_mass
    exact positive_mass_not_integrable replacement positive_mass integrable
  rw [integral_congr_ae (zero_mass_payoff_zero replacement zero_mass)]
  simp

theorem lawAt_incumbent : lawAt falseAction = profileLaw incumbent := by
  have unchanged : Function.update incumbent false falseAction = incumbent := by
    funext i
    cases i <;> rfl
  rw [lawAt, unchanged]

theorem incumbent_payoff_zero (i : Bool) :
    game.payoff i =ᵐ[profileLaw incumbent] fun _ => 0 := by
  cases i
  · rw [← lawAt_incumbent]
    exact zero_mass_payoff_zero falseAction (by simp [falseAction])
  · exact Filter.Eventually.of_forall fun _ => rfl

theorem incumbent_integrable : game.MixedPayoffsIntegrable incumbent := by
  intro i
  exact (integrable_const (0 : ℝ)).congr (incumbent_payoff_zero i).symm

theorem incumbent_expected_payoff_zero (i : Bool) :
    game.mixedExtension.payoff i incumbent = 0 := by
  change (∫ action, game.payoff i action ∂profileLaw incumbent) = 0
  rw [integral_congr_ae (incumbent_payoff_zero i)]
  simp

/-- This is the current convention: only integrable deviator payoffs are
compared, and each such deviation here has payoff zero. -/
theorem incumbent_isMixedNash : game.IsMixedNash incumbent := by
  rw [StrategicGame.isMixedNash_iff]
  refine ⟨incumbent_integrable, ?_⟩
  intro i replacement integrable
  cases i
  · change (∫ action, game.payoff false action ∂lawAt replacement) ≤
      game.mixedExtension.payoff false incumbent
    simpa only [incumbent_expected_payoff_zero] using
      (integrable_deviation_payoff_zero replacement integrable).le
  · change (∫ action, (0 : ℝ)
      ∂profileLaw (Function.update incumbent true replacement)) ≤
      game.mixedExtension.payoff true incumbent
    rw [incumbent_expected_payoff_zero]
    simp

def deviated : StrategicGame.MixedStrategy Action :=
  Function.update incumbent false trueAction

theorem deviation_nonnegative_gain :
    ∀ action, 0 ≤ game.payoff false action := gain_nonnegative

theorem deviation_infinite_gain :
    (∫⁻ action, ENNReal.ofReal (game.payoff false action) ∂profileLaw deviated) = ⊤ :=
  positive_gain_infinite trueAction (by simp [trueAction])

theorem deviation_not_integrable :
    ¬ Integrable (game.payoff false) (profileLaw deviated) :=
  positive_mass_not_integrable trueAction (by simp [trueAction])

theorem deviation_filtered : ¬ game.mixedNashProblem.deviation false incumbent deviated :=
  fun allowed => deviation_not_integrable allowed.2

/-- The real-valued integral is totalized to zero; positive infinity belongs
to the nonnegative extended integral, not to the current payoff carrier. -/
theorem deviation_bochner_payoff_zero : game.mixedExtension.payoff false deviated = 0 :=
  integral_undef deviation_not_integrable

/-- The existing equilibrium carrier can also describe nonnegative extended
comparison, with every unilateral law replacement admitted. -/
def extendedProblem : EquilibriumProblem (StrategicGame.MixedStrategy Action) Bool
    (Measure (∀ i, Action i)) where
  deviation i strategy alternative := ∃ replacement,
    alternative = Function.update strategy i replacement
  value _ := profileLaw
  valid _ := True

def nonnegativeComparison (i : Bool) (alternative incumbentLaw : Measure (∀ i, Action i)) :
    Prop :=
  (∫⁻ action, ENNReal.ofReal (game.payoff i action) ∂alternative) ≤
    ∫⁻ action, ENNReal.ofReal (game.payoff i action) ∂incumbentLaw

theorem incumbent_nonnegative_integral_zero :
    (∫⁻ action, ENNReal.ofReal (game.payoff false action) ∂profileLaw incumbent) = 0 := by
  have same : (fun action ↦ ENNReal.ofReal (game.payoff false action)) =ᵐ[
      profileLaw incumbent] fun _ ↦ (0 : ℝ≥0∞) :=
    (incumbent_payoff_zero false).mono fun _ equal ↦ by simp [equal]
  exact (lintegral_congr_ae same).trans (by simp)

/-- Changing evaluation convention changes the verdict. This is expressed by
the current comparison API, without a new equilibrium carrier. -/
theorem extended_rejects_incumbent :
    ¬ extendedProblem.IsEquilibriumWith nonnegativeComparison incumbent := by
  intro optimal
  have comparison := (optimal.deviation_le false).compares (t := deviated) ⟨trueAction, rfl⟩
  change (∫⁻ action, ENNReal.ofReal (game.payoff false action) ∂profileLaw deviated) ≤
    ∫⁻ action, ENNReal.ofReal (game.payoff false action) ∂profileLaw incumbent at comparison
  rw [deviation_infinite_gain, incumbent_nonnegative_integral_zero] at comparison
  exact (not_le_of_gt (show (0 : ℝ≥0∞) < ⊤ by simp)) comparison

end MathEconLibTest.GameTheory.InfiniteGain
