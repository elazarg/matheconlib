/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Probability.FinDist.Basic

/-!
# Supported outcomes of finite mixtures

A finite mixture assigns positive mass exactly when a positively weighted
component assigns positive mass. The witness retains the contributing index.
These facts need neither an outcome utility nor measure-theoretic structure.
-/

@[expose] public section

namespace MathEconLib.Probability.FinDist

open scoped BigOperators

variable {O A : Type*} [Fintype O] [Fintype A]

/-- Support membership is positive mass. -/
@[simp] theorem mem_support (law : FinDist O) (outcome : O) :
    outcome ∈ law.support ↔ 0 < law outcome := by
  classical
  simp [support]

/-- A finite mixture has positive mass exactly at a supported component outcome. -/
theorem finMixture_pos_iff (weights : FinDist A) (continuation : A → FinDist O)
    (outcome : O) :
    0 < finMixture weights continuation outcome ↔
      ∃ action, 0 < weights action ∧ 0 < continuation action outcome := by
  change 0 < ∑ action, weights.pmf action * (continuation action).pmf outcome ↔ _
  rw [Finset.sum_pos_iff_of_nonneg
    (fun action _ => mul_nonneg (weights.nonneg action) ((continuation action).nonneg outcome))]
  constructor
  · rintro ⟨action, _, positive⟩
    rcases mul_pos_iff.mp positive with both | both
    · exact ⟨action, both⟩
    · exact ((not_lt_of_ge (weights.nonneg action)) both.1).elim
  · rintro ⟨action, first, second⟩
    exact ⟨action, Finset.mem_univ _, mul_pos first second⟩

/-- Mixture support retains an index in the support of the mixing distribution. -/
theorem mem_support_finMixture_iff (weights : FinDist A) (continuation : A → FinDist O)
    (outcome : O) :
    outcome ∈ (finMixture weights continuation).support ↔
      ∃ action ∈ weights.support, outcome ∈ (continuation action).support := by
  simp only [mem_support, finMixture_pos_iff]

/-- Selecting a single component leaves its outcome law unchanged. -/
theorem finMixture_pure [DecidableEq A] (action : A) (continuation : A → FinDist O) :
    finMixture (pure action) continuation = continuation action := by
  apply FinDist.ext
  intro outcome
  rw [finMixture_pmf]
  simp only [pure_pmf]
  simp

/-- Mixing pure outcomes according to a law recovers that law. -/
@[simp] theorem finMixture_pure_right [DecidableEq A] (weights : FinDist A) :
    finMixture weights pure = weights := by
  apply FinDist.ext
  intro outcome
  rw [finMixture_pmf]
  simp

end MathEconLib.Probability.FinDist
