/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.PotentialBounds
public import MathEconLib.RevealedPreference.AfriatGeometry
import Mathlib.Tactic.Linarith

/-!
# Cycle bounds from Afriat inequalities

Afriat support inequalities bound differences of the negative utility potential
on observation indices. Summing those bounds along a finite permutation gives
a cycle restriction without finiteness or sign assumptions on the data.
-/

@[expose] public section

namespace MathEconLib.RevealedPreference

open scoped BigOperators

/-- Negated Afriat supports bound differences of a potential on observations. -/
theorem AfriatInequalities.potentialBounds {T : Type*} {L : ℕ}
    {U lam : T → ℝ} {p q : T → Bundle L} (h : AfriatInequalities U lam p q) :
    PotentialBoundsOn (fun t => -U t)
      (fun t s => -lam t * (dot (p t) (q s) - dot (p t) (q t))) Set.univ := by
  intro s _ t _
  have bound := h s t
  unfold globalAfriatSupport at bound
  dsimp only
  linarith

/-- Every finite cycle of observations satisfies the weighted expenditure restriction. -/
theorem AfriatInequalities.sum_cycle_nonneg {T ι : Type*} {L : ℕ} [Fintype ι]
    {U lam : T → ℝ} {p q : T → Bundle L} (h : AfriatInequalities U lam p q)
    (observations : ι → T) (next : ι ≃ ι) :
    0 ≤ ∑ i, lam (observations i) *
      (dot (p (observations i)) (q (observations (next i))) -
        dot (p (observations i)) (q (observations i))) := by
  have bound := h.potentialBounds.sum_cycle_le_zero observations (fun _ => Set.mem_univ _) next
  simp only [neg_mul, Finset.sum_neg_distrib] at bound
  linarith

end MathEconLib.RevealedPreference
