/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism.Core.WeightedWelfare
public import MathEconLib.Mechanism.Core.Utility
public import MathEconLib.Choice.Maximizers
public import Mathlib.Tactic.NormNum

/-!
# Welfare calibration and monetary units

Independent positive value recodings leave each agent's outcome choices unchanged
on every menu, but change unweighted total-value efficiency. Explicit reciprocal
weights restore the original objective. Scaling valuations while fixing monetary
transfers can change even one agent's action ranking; scaling the whole utility
or both the valuation and transfer preserves the displayed comparisons.

The monetary controls assert comparisons, not participation relative to a fixed
outside utility. Common monetary factors preserve balance; private factors can
destroy it. No welfare conclusion is inferred from ordinal choice alone.
-/

@[expose] public section

namespace MathEconLibTest.Mechanism.WeightedWelfareConsumer

open MathEconLib MathEconLib.Mechanism

def environment : QuasilinearEnvironment Bool (fun _ => Unit) Bool where
  value i _ outcome := if i then (if outcome then 0 else 1) else (if outcome then 2 else 0)

def scale (i : Bool) : ℝ := if i then 3 else 1

theorem scale_positive (i : Bool) : 0 < scale i := by cases i <;> norm_num [scale]

theorem scale_nonzero (i : Bool) : scale i ≠ 0 := ne_of_gt (scale_positive i)

def recodedEnvironment : QuasilinearEnvironment Bool (fun _ => Unit) Bool where
  value i θ outcome := scale i * environment.value i θ outcome

def chooseOutcome (outcome : Bool) : DirectMechanism Bool (fun _ => Unit) Bool where
  outcome _ := outcome
  transfer _ _ := 0

/-- Outcome choice is identical on every menu, including menus with ties. -/
theorem every_agent_menu_unchanged (i : Bool) (θ : Profile (fun _ : Bool => Unit))
    (menu : Set Bool) :
    Choice.maximizers (Preferences.Preference.ofUtility (recodedEnvironment.value i θ)) menu =
      Choice.maximizers (Preferences.Preference.ofUtility (environment.value i θ)) menu :=
  Choice.maximizers_ofUtility_comp_strictMono (environment.value i θ)
    (fun value : ℝ => scale i * value) (strictMono_mul_left_of_pos (scale_positive i)) menu

theorem original_true_efficient : DirectMechanism.IsEfficient environment (chooseOutcome true) := by
  rw [DirectMechanism.isEfficient_iff]
  intro θ outcome
  cases outcome <;>
    norm_num [QuasilinearEnvironment.totalValue, Fintype.sum_bool, environment, chooseOutcome]

theorem recoded_false_efficient :
    DirectMechanism.IsEfficient recodedEnvironment (chooseOutcome false) := by
  rw [DirectMechanism.isEfficient_iff]
  intro θ outcome
  cases outcome <;>
    norm_num [QuasilinearEnvironment.totalValue, Fintype.sum_bool,
      recodedEnvironment, environment, scale, chooseOutcome]

theorem recoded_true_not_efficient :
    ¬ DirectMechanism.IsEfficient recodedEnvironment (chooseOutcome true) := by
  intro efficient
  have comparison := (DirectMechanism.isEfficient_iff _ _).mp efficient (fun _ => ()) false
  norm_num [QuasilinearEnvironment.totalValue, Fintype.sum_bool,
    recodedEnvironment, environment, scale, chooseOutcome] at comparison

/-- Positive reciprocal weights restore the original selection through native efficiency. -/
theorem reciprocal_weights_restore :
    ∀ θ, IsMaxOn (recodedEnvironment.weightedTotalValue (fun i => 1 / scale i) θ)
      Set.univ true := by
  apply (DirectMechanism.isEfficient_iff_reciprocal_weighted
    (E := environment) (E' := recodedEnvironment) (scale := scale)
    (offset := fun _ _ => 0) (chooseOutcome true) scale_nonzero ?_).mp original_true_efficient
  intro i θ outcome
  simp only [recodedEnvironment, add_zero]

def buyMechanism : MathEconLib.Mechanism Unit (fun _ => Bool) Bool where
  outcome report := report ()
  transfer _ report := if report () then -1 else 0

def buyEnvironment : QuasilinearEnvironment Unit (fun _ => Unit) Bool where
  value _ _ outcome := if outcome then 2 else 0

noncomputable def quarterValue : QuasilinearEnvironment Unit (fun _ => Unit) Bool where
  value i θ outcome := (1 / 4 : ℝ) * buyEnvironment.value i θ outcome

noncomputable def quarterTransfers : MathEconLib.Mechanism Unit (fun _ => Bool) Bool where
  outcome := buyMechanism.outcome
  transfer i report := (1 / 4 : ℝ) * buyMechanism.transfer i report

noncomputable def fullQuarterUtility : Unit → (Unit → Unit) → (Bool × (Unit → ℝ)) → ℝ :=
  utilityFromOwnTransfer
    (fun i θ outcome transfer => (1 / 4 : ℝ) * (buyEnvironment.value i θ outcome + transfer))

/-- Fixing money while scaling only value reverses the actual buy/decline comparison. -/
theorem valuation_only_changes_ranking :
    buyEnvironment.utility buyMechanism () (fun _ => ()) (fun _ => false) <
      buyEnvironment.utility buyMechanism () (fun _ => ()) (fun _ => true) ∧
    quarterValue.utility buyMechanism () (fun _ => ()) (fun _ => true) <
      quarterValue.utility buyMechanism () (fun _ => ()) (fun _ => false) := by
  norm_num [QuasilinearEnvironment.utility, buyEnvironment, buyMechanism, quarterValue]

/-- Both complete utility recoding and matched value/transfer scaling keep the buy comparison. -/
theorem complete_recodings_preserve_ranking :
    (buyMechanism.toStrategicGame fullQuarterUtility (fun _ => ())).payoff () (fun _ => false) <
      (buyMechanism.toStrategicGame fullQuarterUtility (fun _ => ())).payoff () (fun _ => true) ∧
    quarterValue.utility quarterTransfers () (fun _ => ()) (fun _ => false) <
      quarterValue.utility quarterTransfers () (fun _ => ()) (fun _ => true) := by
  norm_num [toStrategicGame_payoff, fullQuarterUtility, utilityFromOwnTransfer,
    QuasilinearEnvironment.utility, buyEnvironment, buyMechanism, quarterValue, quarterTransfers]

def balancedMechanism : MathEconLib.Mechanism Bool (fun _ => Unit) Unit where
  outcome _ := ()
  transfer i _ := if i then -1 else 1

def scaledBalance (factors : Bool → ℝ) : MathEconLib.Mechanism Bool (fun _ => Unit) Unit where
  outcome := balancedMechanism.outcome
  transfer i report := factors i * balancedMechanism.transfer i report

theorem original_budget_balanced : balancedMechanism.IsBudgetBalanced := by
  intro report
  norm_num [balancedMechanism, Fintype.sum_bool]

/-- Private factors two and one turn zero net transfers into a positive net payment to agents. -/
theorem private_scale_not_balanced :
    ¬ (scaledBalance (fun i => if i then 1 else 2)).IsBudgetBalanced := by
  intro balanced
  have impossible := balanced (fun _ => ())
  norm_num [scaledBalance, balancedMechanism, Fintype.sum_bool] at impossible

/-- Balance is a homogeneous equality, so every common factor preserves it. -/
theorem common_scale_balanced (factor : ℝ) :
    (scaledBalance (fun _ => factor)).IsBudgetBalanced := by
  intro report
  change (∑ i, factor * balancedMechanism.transfer i report) = 0
  rw [← Finset.mul_sum, original_budget_balanced report, mul_zero]

theorem positive_common_scale_balanced : (scaledBalance (fun _ => 2)).IsBudgetBalanced :=
  common_scale_balanced 2

end MathEconLibTest.Mechanism.WeightedWelfareConsumer
