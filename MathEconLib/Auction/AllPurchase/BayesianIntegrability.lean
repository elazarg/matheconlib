/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.AllPurchase.LinearScarcity
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability of linear-scarcity auction payments and utilities

A fixed deviation bid needs only integrable opponents' purchases: linear
scarcity makes its payment affine in their total purchase. Realized bids
require a product estimate. Monotonicity on the bounded realized type interval
provides an essential bound for both purchases and values, so native bounded
factor multiplication proves realized utility integrable. Negative bids and
values are allowed, and no independence or atomlessness is used.
-/

@[expose] public section

namespace MathEconLib

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {n : ℕ}


namespace LinearScarcityAuction

variable (A : LinearScarcityAuction Ω n)

/-- The native payment is measurable on the entire real action-profile space. -/
theorem measurable_payment (i : Fin n) :
    Measurable (fun bids : Fin n → ℝ => A.rules.payment i bids) := by
  have total : Measurable (fun bids : Fin n → ℝ => ∑ j, bids j) :=
    Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)
  simp_rw [A.spec.payment_eq, A.scarcity_is_linear]
  exact (measurable_const.sub (measurable_const.sub (total.const_mul A.α_coeff))).mul
    (measurable_pi_apply i)

/-- A fixed bid has integrable payment whenever opponents' purchases are integrable. -/
theorem integrable_payment_strat (strategy : ℝ → ℝ)
    (integrable : ∀ j, Integrable (fun ω => strategy (A.θ j ω)) ℙ)
    (i : Fin n) (bid : ℝ) :
    Integrable (fun ω => A.rules.payment i
      (Function.update (fun j => strategy (A.θ j ω)) i bid)) ℙ := by
  have opponents : Integrable
      (fun ω => ∑ j ∈ Finset.univ.erase i, strategy (A.θ j ω)) ℙ :=
    integrable_finsetSum _ (fun j _ => integrable j)
  simp_rw [A.spec.payment_eq, A.scarcity_is_linear,
    Finset.sum_update_univ, Function.update_self]
  exact ((integrable_const _).sub ((integrable_const _).sub
    (((integrable_const bid).add opponents).const_mul A.α_coeff))).mul_const bid

/-- Bounded monotone prescribed bids give integrable realized quasilinear utility. -/
theorem integrable_realized_utility [NeZero n] [A.HasIdenticalTypes] [A.HasBoundedTypes]
    (strategy : ℝ → ℝ) (measurable : Measurable strategy)
    (monotone : MonotoneOn strategy (Icc A.lowestType A.highestType)) (i : Fin n) :
    Integrable (fun ω => (Auction.valuationEnvironment n).utility A.rules i
      (fun j => A.θ j ω) (fun j => strategy (A.θ j ω))) ℙ := by
  have purchases (j : Fin n) : MemLp (fun ω => strategy (A.θ j ω)) ∞ ℙ :=
    A.toAuction.memLp_top_comp_type_of_monotoneOn strategy measurable monotone j
  have values : MemLp (A.θ i) ∞ ℙ :=
    A.toAuction.memLp_top_comp_type_of_monotoneOn id measurable_id
      (fun _ _ _ _ weak => weak) i
  have integrablePurchases (j : Fin n) : Integrable (fun ω => strategy (A.θ j ω)) ℙ :=
    A.toAuction.integrable_comp_type_of_monotoneOn strategy measurable monotone j
  have total : Integrable (fun ω => ∑ j, strategy (A.θ j ω)) ℙ :=
    integrable_finsetSum _ (fun j _ => integrablePurchases j)
  have unitCost : Integrable
      (fun ω => A.spec.price - (A.φ_bar - A.α_coeff * ∑ j, strategy (A.θ j ω))) ℙ :=
    (integrable_const _).sub ((integrable_const _).sub (total.const_mul A.α_coeff))
  have payment : Integrable
      (fun ω => A.rules.payment i (fun j => strategy (A.θ j ω))) ℙ := by
    simp_rw [A.spec.payment_eq, A.scarcity_is_linear]
    exact unitCost.mul_of_top_left (purchases i)
  have allocation : Integrable
      (fun ω => A.rules.outcome (fun j => strategy (A.θ j ω)) i) ℙ := by
    refine (integrable_const (1 : ℝ)).mono'
      ((A.outcome_measurable i).comp
        (Measurable.of_eval fun j => measurable.comp (A.θ_measurable j))).aestronglyMeasurable ?_
    apply ae_of_all
    intro ω
    have bounds := A.spec.isUnitIntervalAllocation i (fun j => strategy (A.θ j ω))
    rw [Real.norm_eq_abs, abs_of_nonneg bounds.1]
    exact bounds.2
  have valueAllocation : Integrable
      (fun ω => A.θ i ω * A.rules.outcome (fun j => strategy (A.θ j ω)) i) ℙ :=
    allocation.mul_of_top_right values
  simp_rw [Mechanism.QuasilinearEnvironment.utility_eq_value_sub_payment]
  change Integrable (fun ω => A.θ i ω * A.rules.outcome
    (fun j => strategy (A.θ j ω)) i - A.rules.payment i (fun j => strategy (A.θ j ω))) ℙ
  exact valueAllocation.sub payment

end LinearScarcityAuction
end MathEconLib
