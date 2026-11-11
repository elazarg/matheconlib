/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# Strong Nash with vector payoffs

Joint coordination has an ordinary equilibrium that a joint change defeats.
Local comparison suffices at the successful profile despite the ambient
product order being partial. An actual incomparable deviation separates weak
strong-Nash rejection from absence of unanimous strict improvement.
-/

@[expose] public section

namespace MathEconLibTest.GameTheory.StrongNashComparability

open MathEconLib.GameTheory

def coordination : StrategicGame Bool (fun _ ↦ Bool) (ℝ × ℝ) where
  payoff _ actions := if actions false && actions true then (1, 1) else (0, 0)

def low : Bool → Bool := fun _ ↦ false

def high : Bool → Bool := fun _ ↦ true

theorem low_isNash : coordination.IsNash low := by
  rw [StrategicGame.isNash_iff]
  intro i replacement
  cases i <;> cases replacement <;> norm_num [coordination, low, Function.update]

theorem low_not_isStrongNash : ¬ coordination.IsStrongNash low := by
  intro strong
  have different : high ≠ low := by
    intro equal
    have impossible := congrFun equal false
    simp [high, low] at impossible
  obtain ⟨i, _, rejection⟩ := strong high different
  norm_num [coordination, high, low] at rejection

theorem high_payoff_le (alternative : Bool → Bool) (i : Bool) :
    coordination.payoff i alternative ≤ coordination.payoff i high := by
  change (if alternative false && alternative true then (1, 1) else (0, 0)) ≤
    ((1, 1) : ℝ × ℝ)
  split <;> norm_num

theorem high_comparable (alternative : Bool → Bool) (_different : alternative ≠ high)
    (i : Bool) (_changed : high i ≠ alternative i) :
    coordination.payoff i alternative ≤ coordination.payoff i high ∨
      coordination.payoff i high ≤ coordination.payoff i alternative := by
  exact Or.inl (high_payoff_le alternative i)

theorem high_isStrongNash : coordination.IsStrongNash high := by
  apply (coordination.isStrongNash_iff_not_lt_of_comparable high high_comparable).mpr
  intro alternative different strict
  have changed : ∃ i, high i ≠ alternative i := by
    by_contra unchanged
    push Not at unchanged
    exact different (funext fun i ↦ (unchanged i).symm)
  obtain ⟨i, changed⟩ := changed
  exact (not_lt_of_ge (high_payoff_le alternative i)) (strict i changed)

def crossing : StrategicGame Unit (fun _ ↦ Bool) (ℝ × ℝ) where
  payoff _ actions := if actions () then (1, 0) else (0, 1)

def incumbent : Unit → Bool := fun _ ↦ false

theorem crossing_no_strict_gain :
    ∀ alternative ≠ incumbent, ¬ ∀ i, incumbent i ≠ alternative i →
      crossing.payoff i incumbent < crossing.payoff i alternative := by
  intro alternative different strict
  have changed : incumbent () ≠ alternative () := by
    intro same
    apply different
    funext i
    cases i
    exact same.symm
  have gain := strict () changed
  cases choice : alternative () <;>
    norm_num [crossing, incumbent, choice, lt_iff_le_not_ge] at gain

theorem crossing_not_isStrongNash : ¬ crossing.IsStrongNash incumbent := by
  intro strong
  obtain ⟨i, _, rejection⟩ := strong (fun _ ↦ true) (by
    intro same
    have impossible := congrFun same ()
    simp [incumbent] at impossible)
  norm_num [crossing, incumbent] at rejection

theorem crossing_incomparable :
    ¬ (crossing.payoff () (fun _ ↦ true) ≤ crossing.payoff () incumbent ∨
      crossing.payoff () incumbent ≤ crossing.payoff () (fun _ ↦ true)) := by
  norm_num [crossing, incumbent]

theorem comparability_cannot_be_dropped :
    ¬ (crossing.IsStrongNash incumbent ↔
      ∀ alternative ≠ incumbent, ¬ ∀ i, incumbent i ≠ alternative i →
        crossing.payoff i incumbent < crossing.payoff i alternative) :=
  fun equivalence ↦ crossing_not_isStrongNash (equivalence.mpr crossing_no_strict_gain)

end MathEconLibTest.GameTheory.StrongNashComparability
