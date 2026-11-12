/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.WitnessLift
public import MathEconLib.GameTheory.Strategic.Basic
public import MathEconLibTest.GameTheory.StrongNashComparability

/-!
# Unilateral improvements as collective blocking witnesses

A unilateral strict improvement is a collective improvement in which only
the deviator changes. The witness retains that precise profile update.
Identifying absence of strict collective gains with weak-rejection strong
Nash requires the separate local-comparability hypothesis.
-/

@[expose] public section

namespace MathEconLibTest.AbstractionExperiments.CoalitionWitnessConsumer

open MathEconLib MathEconLib.GameTheory

variable {I : Type*} {A : I → Type*} {V : Type*} [Preorder V] [DecidableEq I]
  (G : StrategicGame I A V)

/-- A genuinely changed profile strictly benefits every player who changes. -/
def collectiveBlock (a b : ∀ i, A i) : Prop :=
  b ≠ a ∧ ∀ i, a i ≠ b i → G.payoff i a < G.payoff i b

/-- A unilateral proposal carries its deviator and replacement action. -/
def unilateralBlock (a : ∀ i, A i) (proposal : Sigma A) : Prop :=
  G.payoff proposal.1 a < G.payoff proposal.1 (Function.update a proposal.1 proposal.2)

/-- Unilateral proposals lift to collective witnesses with the exact updated profile. -/
def unilateralLift : WitnessLift (collectiveBlock G) (unilateralBlock G) where
  state := id
  related a proposal b := b = Function.update a proposal.1 proposal.2
  covers := by
    intro a proposal profitable
    refine ⟨Function.update a proposal.1 proposal.2, ?_, ?_, ?_⟩
    · rfl
    · intro unchanged
      change G.payoff proposal.1 a <
        G.payoff proposal.1 (Function.update a proposal.1 proposal.2) at profitable
      rw [unchanged] at profitable
      exact (lt_irrefl _) profitable
    · intro i changed
      by_cases equal : i = proposal.1
      · subst i
        exact profitable
      · exact (changed (Function.update_of_ne equal proposal.2 a).symm).elim

/-- The same witness transport used by matching applies to coalition gain tests. -/
theorem no_collective_implies_no_unilateral {a : ∀ i, A i}
    (unblocked : ∀ b, ¬ collectiveBlock G a b) : ∀ proposal, ¬ unilateralBlock G a proposal :=
  (unilateralLift G).transport unblocked

omit [DecidableEq I] in
/-- Native weak-rejection strong Nash agrees with the strict blocking view
under comparability of exactly the incumbent/deviation pairs. -/
theorem strongNash_iff_no_collective (a : ∀ i, A i)
    (comparable : ∀ b ≠ a, ∀ i, a i ≠ b i →
      G.payoff i b ≤ G.payoff i a ∨ G.payoff i a ≤ G.payoff i b) :
    G.IsStrongNash a ↔ ∀ b, ¬ collectiveBlock G a b := by
  rw [G.isStrongNash_iff_not_lt_of_comparable a comparable]
  exact ⟨fun h b block => h b block.1 block.2,
    fun h b different strict => h b ⟨different, strict⟩⟩

/-- A state-independent relation cannot characterize exact updates for every incumbent. -/
theorem no_unrooted_exact_update :
    ¬ ∃ related : (Bool × Bool) → (Bool → Bool) → Prop,
      ∀ a proposal b, related proposal b ↔ b = Function.update a proposal.1 proposal.2 := by
  rintro ⟨related, exactUpdate⟩
  have known : related (false, true) (Function.update (fun _ => false) false true) :=
    (exactUpdate (fun _ => false) (false, true) _).mpr rfl
  have impossible := (exactUpdate (fun _ => true) (false, true) _).mp known
  have opposite := congrFun impossible true
  exact Bool.false_ne_true opposite

open MathEconLibTest.GameTheory.StrongNashComparability

/-- Coordination has no unilateral strict gain, although both players can gain together. -/
theorem unilateral_absence_does_not_imply_collective_absence :
    (∀ proposal, ¬ unilateralBlock coordination low proposal) ∧
      collectiveBlock coordination low high := by
  constructor
  · rintro ⟨i, action⟩ profitable
    exact (not_lt_of_ge ((StrategicGame.isNash_iff _ _).mp low_isNash i action)) profitable
  · refine ⟨?_, ?_⟩
    · intro equal
      have impossible := congrFun equal false
      exact Bool.false_ne_true impossible.symm
    · intro i _
      norm_num [coordination, low, high, lt_iff_le_not_ge]

end MathEconLibTest.AbstractionExperiments.CoalitionWitnessConsumer
