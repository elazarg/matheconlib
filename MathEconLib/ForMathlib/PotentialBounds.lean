/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Increments bounded by potential differences

The point type has no algebraic structure. Each increment from a base point
to an alternative is bounded by the corresponding change in a potential.
Summing along a finite permutation cancels the potential differences.
-/

@[expose] public section

namespace MathEconLib

/-- Increments are oriented from the second quantified point to the first. -/
def PotentialBoundsOn {A : Type*} (U : A → ℝ) (increment : A → A → ℝ)
    (S : Set A) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, increment y x ≤ U x - U y

namespace PotentialBoundsOn

open scoped BigOperators

/-- A finite cycle of bounded increments cannot have positive total increment. -/
theorem sum_cycle_le_zero {A : Type*} {U : A → ℝ} {increment : A → A → ℝ} {S : Set A}
    (h : PotentialBoundsOn U increment S) {ι : Type*} [Fintype ι]
    (points : ι → A) (members : ∀ i, points i ∈ S) (next : ι ≃ ι) :
    (∑ i, increment (points i) (points (next i))) ≤ 0 := by
  calc
    _ ≤ ∑ i, (U (points (next i)) - U (points i)) :=
      Finset.sum_le_sum fun i _ => h _ (members (next i)) _ (members i)
    _ = 0 := by
      rw [Finset.sum_sub_distrib, next.sum_comp (fun i => U (points i)), sub_self]

end PotentialBoundsOn

end MathEconLib
