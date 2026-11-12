/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.Typeclasses

/-!
# Winning probabilities outside the range of monotone bids

With bounded types and a common monotone strategy, a bid at or below the lowest
prescribed bid cannot strictly outbid an opponent. This uses an actual opponent,
so requires at least two bidders. The conclusion is pointwise before integration
and needs no measurability, independence or atomlessness assumption. Bids above
the highest prescribed bid always win, even with only one bidder.
-/

@[expose] public section

namespace MathEconLib.Auction

open Set MeasureTheory ProbabilityTheory MathEconLib.Mechanism.Auctions

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {n : ℕ} [NeZero n] (A : Auction Ω n) [A.HasIdenticalTypes] [A.HasBoundedTypes]

/-- A bid below every prescribed opponent bid never receives the strict-highest prize. -/
theorem q_strat_eq_zero_of_le_lowest [n.AtLeastTwo]
    (highest : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    {strategy : ℝ → ℝ} (monotone : MonotoneOn strategy (Icc A.lowestType A.highestType))
    (i : Fin n) {bid : ℝ} (below : bid ≤ strategy A.lowestType) :
    A.q_strat strategy i bid = 0 := by
  have zero (ω : Ω) :
      A.rules.outcome (Function.update (fun j => strategy (A.θ j ω)) i bid) i = 0 := by
    have rule := congrFun (highest i) (Function.update (fun j => strategy (A.θ j ω)) i bid)
    dsimp only at rule
    rw [rule]
    apply Set.indicator_of_notMem
    intro wins
    obtain ⟨j, distinct⟩ := exists_ne i
    have member : A.θ j ω ∈ Icc A.lowestType A.highestType := by
      simpa only [A.θmin_eq_lowestType, A.θmax_eq_highestType] using
        (HasBoundedTypes.θ_in (A := A) j ω)
    have lower := monotone ⟨le_rfl, member.1.trans member.2⟩ member member.1
    have strict := wins j distinct
    simp only [Function.update_of_ne distinct, Function.update_self] at strict
    exact (not_lt_of_ge (below.trans lower)) strict
  simp only [q_strat, zero, integral_zero]

/-- A bid strictly above every prescribed opponent bid receives the prize surely. -/
theorem q_strat_eq_one_of_highest_lt
    (highest : UsesStrictHighestBidAllocation A.rules (fun o i => o i))
    {strategy : ℝ → ℝ} (monotone : MonotoneOn strategy (Icc A.lowestType A.highestType))
    (i : Fin n) {bid : ℝ} (above : strategy A.highestType < bid) :
    A.q_strat strategy i bid = 1 := by
  have one (ω : Ω) :
      A.rules.outcome (Function.update (fun j => strategy (A.θ j ω)) i bid) i = 1 := by
    have rule := congrFun (highest i) (Function.update (fun j => strategy (A.θ j ω)) i bid)
    dsimp only at rule
    rw [rule]
    apply Set.indicator_of_mem
    intro j distinct
    have member : A.θ j ω ∈ Icc A.lowestType A.highestType := by
      simpa only [A.θmin_eq_lowestType, A.θmax_eq_highestType] using
        (HasBoundedTypes.θ_in (A := A) j ω)
    have upper := monotone member ⟨member.1.trans member.2, le_rfl⟩ member.2
    simpa only [Function.update_of_ne distinct, Function.update_self] using upper.trans_lt above
  simp only [q_strat, one, integral_const, probReal_univ, one_smul]

end MathEconLib.Auction
