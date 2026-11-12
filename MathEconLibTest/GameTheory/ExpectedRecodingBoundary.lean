/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Choice.Maximizers
public import MathEconLib.Probability.FinDist.Expect
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Ordinal outcome utility does not determine expected-lottery choices

Two utilities give the same ranking and all greatest choices on pure-outcome
menus. They rank a fixed lottery against a fixed sure outcome in opposite ways.
The utilities are not positive-affine recodings of each other. No comparison of
lotteries is inferred solely from the ordinal pure-outcome representation.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.AbstractionExperiments.ExpectedRecodingBoundary

open MathEconLib MathEconLib.Probability

def utility : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | _ => 3

def recodedUtility : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | _ => 3 / 2

theorem utility_strictMono : StrictMono utility := by
  intro first second increasing
  fin_cases first <;> fin_cases second <;> norm_num [utility] at *

theorem recoded_strictMono : StrictMono recodedUtility := by
  intro first second increasing
  fin_cases first <;> fin_cases second <;> norm_num [recodedUtility] at *

/-- Every menu, including the empty menu, gives exactly the same pure choices. -/
theorem all_menu_choices_equal (menu : Set (Fin 3)) :
    Choice.maximizers (Preferences.Preference.ofUtility recodedUtility) menu =
      Choice.maximizers (Preferences.Preference.ofUtility utility) menu := by
  calc
    _ = Choice.maximizers (Preferences.Preference.ofUtility (id : Fin 3 → Fin 3)) menu :=
      Choice.maximizers_ofUtility_comp_strictMono id recodedUtility recoded_strictMono menu
    _ = _ :=
      (Choice.maximizers_ofUtility_comp_strictMono id utility utility_strictMono menu).symm

def lottery : FinDist (Fin 3) :=
  FinDist.mixture ⟨1 / 2, by norm_num, by norm_num⟩ (FinDist.pure 0) (FinDist.pure 2)

/-- Recoding primitive outcome utility reverses the actual expected-payoff comparison. -/
theorem expected_comparison_reverses :
    (FinDist.pure 1).expect utility < lottery.expect utility ∧
      lottery.expect recodedUtility < (FinDist.pure 1).expect recodedUtility := by
  constructor <;>
    norm_num [lottery, FinDist.expect_mixture, FinDist.expect_pure,
      utility, recodedUtility, smul_eq_mul]

/-- No change of origin and positive scale relates these ordinal representations. -/
theorem not_positive_affine :
    ¬ ∃ scale offset : ℝ, 0 < scale ∧
      ∀ outcome, recodedUtility outcome = scale * utility outcome + offset := by
  rintro ⟨scale, offset, _, represents⟩
  have atZero := represents 0
  have atOne := represents 1
  have atTwo := represents 2
  norm_num [utility, recodedUtility] at atZero atOne atTwo
  linarith

end MathEconLibTest.AbstractionExperiments.ExpectedRecodingBoundary
