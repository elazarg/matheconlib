/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.BayesianRevelation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Revelation for a posted-price mechanism with an unused costly action

A low type declines, a high type buys for one, and neither type uses the action
charging three for the same good. Both generic proofs produce truthful Bayesian
implementation under the same fair prior, without surjective strategy maps.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.GameTheory.RevelationConsumer

open MathEconLib.GameTheory MathEconLib.Mechanism MeasureTheory
open MathEconLibTest.GameTheory.BayesianRevelation

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSingletonClass Bool := ⟨fun _ ↦ trivial⟩
local instance : MeasurableSpace (Fin 3) := ⊤

def indirect : MathEconLib.Mechanism Unit (fun _ ↦ Fin 3) Bool where
  outcome actions := if actions () = 0 then false else true
  transfer _ actions := if actions () = 0 then 0 else if actions () = 1 then -1 else -3

def utility (_ : Unit) (types : Unit → Bool) (consequence : Bool × (Unit → ℝ)) : ℝ :=
  (if types () then 2 else 0) * (if consequence.1 then 1 else 0) + consequence.2 ()

local notation "G" => MathEconLib.Mechanism.toBayesianGame indirect utility

def strategy : (G).Strategy :=
  fun _ ↦ ⟨fun high ↦ if high then 1 else 0, measurable_from_top⟩

def prior : Measure (Unit → Bool) :=
  (1 / 2 : ENNReal) • Measure.dirac (fun _ ↦ false) +
    (1 / 2 : ENNReal) • Measure.dirac (fun _ ↦ true)

instance : IsProbabilityMeasure prior where
  measure_univ := by norm_num [prior, ENNReal.inv_two_add_inv_two]

/-- Conditional optimality is checked at both types against every original action. -/
theorem pointwise_best (types : Unit → Bool) (actions : Unit → Fin 3) :
    (G).payoff () actions types ≤
      (G).payoff () ((G).measurableActionProfile strategy types) types := by
  obtain ⟨high, rfl⟩ : ∃ high, types = fun _ ↦ high :=
    ⟨types (), funext fun i ↦ by cases i; rfl⟩
  obtain ⟨action, rfl⟩ : ∃ action, actions = fun _ ↦ action :=
    ⟨actions (), funext fun i ↦ by cases i; rfl⟩
  cases high <;> fin_cases action <;>
    norm_num [indirect, utility, BayesianGame.measurableActionProfile, strategy]

/-- Finite types make every realized payoff integrable; the pointwise bounds integrate. -/
theorem original_isBNE : (G).IsBNE prior strategy := by
  rw [BayesianGame.isBNE_iff]
  refine ⟨?_, fun _ ↦ Integrable.of_finite⟩
  intro i alternative _ integrable
  cases i
  exact integral_mono integrable Integrable.of_finite
    (fun types ↦ pointwise_best types ((G).measurableActionProfile alternative types))

/-- The wasteful action has no preimage under the chosen strategy. -/
theorem strategy_not_surjective : ¬ Function.Surjective (strategy ()).1 := by
  intro covers
  obtain ⟨high, equal⟩ := covers 2
  cases high <;> norm_num [strategy] at equal

local notation "D" => MathEconLib.Mechanism.toBayesianGame
  (MathEconLib.Mechanism.comap indirect (fun i ↦ Subtype.val (strategy i))) utility

theorem truthful_by_record : (D).IsBNE prior (truthful indirect utility strategy) :=
  record_route indirect utility prior strategy original_isBNE

theorem truthful_by_direct : (D).IsBNE prior (truthful indirect utility strategy) :=
  direct_route indirect utility prior strategy original_isBNE

theorem source_with_error (error : ℝ) (nonnegative : 0 ≤ error) :
    ((G).bneProblem prior).IsEquilibriumWith (fun _ x y ↦ x ≤ y + error) strategy := by
  refine ⟨original_isBNE.integrable, fun i alternative allowed ↦ ?_⟩
  exact (original_isBNE.deviation_le i alternative allowed).trans
    (le_add_of_nonneg_right nonnegative)

theorem truthful_error_by_record (error : ℝ) (nonnegative : 0 ≤ error) :
    ((D).bneProblem prior).IsEquilibriumWith (fun _ x y ↦ x ≤ y + error)
      (truthful indirect utility strategy) :=
  record_comparison_route indirect utility prior strategy _ (source_with_error error nonnegative)

theorem truthful_error_by_direct (error : ℝ) (nonnegative : 0 ≤ error) :
    ((D).bneProblem prior).IsEquilibriumWith (fun _ x y ↦ x ≤ y + error)
      (truthful indirect utility strategy) :=
  direct_comparison_route indirect utility prior strategy _ (source_with_error error nonnegative)

end MathEconLibTest.GameTheory.RevelationConsumer
