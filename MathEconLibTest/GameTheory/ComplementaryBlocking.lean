/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Matching.Contracts.Basic

/-!
# Complementary contracts require a joint blocking test

One buyer accepts two contracts together and rejects either contract alone.
Each seller accepts its own available contract. The empty outcome is individually
rational and has no single-contract block, while the two contracts jointly block.
-/

@[expose] public section

namespace MathEconLibTest.AbstractionExperiments.ComplementaryBlocking

open Set MathEconLib.Choice MathEconLib.Matching

noncomputable def complementaryBuyer : ChoiceFunction Bool := by
  classical
  exact
    { toFun := fun offered => if offered = univ then offered else ∅
      choose_subset := by
        intro offered
        split_ifs
        · exact Subset.rfl
        · exact empty_subset _ }

def ownContract (seller : Bool) : ChoiceFunction Bool where
  toFun offered := {contract ∈ offered | contract = seller}
  choose_subset _ _ chosen := chosen.1

noncomputable def market : Market Unit Bool Bool where
  buyer _ := ()
  seller contract := contract
  choiceB _ := complementaryBuyer
  choiceS := ownContract
  buyer_eq_of_mem := by intro b _ _ _; cases b; rfl
  seller_eq_of_mem := by intro _ _ _ chosen; exact chosen.2

private theorem singleton_ne_univ (contract : Bool) : ({contract} : Set Bool) ≠ univ := by
  intro equal
  have impossible := congrArg (fun offered : Set Bool => (!contract) ∈ offered) equal
  cases contract <;> simp at impossible

@[simp] theorem buyer_empty : complementaryBuyer ∅ = ∅ := by
  classical
  change (if (∅ : Set Bool) = univ then ∅ else ∅) = ∅
  split_ifs <;> rfl

@[simp] theorem buyer_univ : complementaryBuyer univ = univ := by
  classical
  change (if (univ : Set Bool) = univ then univ else ∅) = univ
  exact ite_eq_left rfl

@[simp] theorem buyer_singleton (contract : Bool) : complementaryBuyer {contract} = ∅ := by
  classical
  change (if ({contract} : Set Bool) = univ then {contract} else ∅) = ∅
  exact ite_eq_right (singleton_ne_univ contract)

theorem empty_indRational : market.IndRational ∅ := by
  constructor
  · intro buyer
    ext contract
    simp [market, Market.buyerSide]
  · intro seller
    rfl

/-- Nonemptiness, novelty, and both sides' consent are supplied explicitly. -/
theorem joint_blocks_empty : market.Blocks ∅ univ := by
  refine ⟨⟨false, mem_univ _⟩, by simp, ?_, ?_⟩
  · intro buyer contract _
    change contract ∈ complementaryBuyer (∅ ∪ univ)
    rw [empty_union, buyer_univ]
    exact mem_univ _
  · intro seller contract chosen
    change contract ∈ (∅ ∪ univ : Set Bool) ∧ contract = seller
    exact ⟨Or.inr (mem_univ _), chosen.2⟩

theorem singleton_not_blocks_empty (contract : Bool) : ¬ market.Blocks ∅ {contract} := by
  intro block
  have buyerConsent := (market.blocks_singleton_iff.mp block).2.1
  change contract ∈ complementaryBuyer (insert contract ∅) at buyerConsent
  rw [insert_empty_eq] at buyerConsent
  rw [buyer_singleton] at buyerConsent
  exact buyerConsent

theorem empty_pairwiseStable : market.PairwiseStable ∅ :=
  ⟨empty_indRational, singleton_not_blocks_empty⟩

theorem empty_not_stable : ¬ market.Stable ∅ := by
  intro stable
  exact stable.2 univ joint_blocks_empty

/-- A contract accepted in the full menu is rejected after the other is removed. -/
theorem buyer_not_substitutable : ¬ complementaryBuyer.Substitutable := by
  intro substitute
  have chosen : false ∈ complementaryBuyer univ := by rw [buyer_univ]; exact mem_univ _
  have singletonChosen := substitute.mem_of_subset
    (subset_univ ({false} : Set Bool)) chosen (by simp)
  rw [buyer_singleton] at singletonChosen
  exact singletonChosen

theorem market_not_substitutable : ¬ market.Substitutable := by
  intro substitute
  exact buyer_not_substitutable (substitute.1 ())

end MathEconLibTest.AbstractionExperiments.ComplementaryBlocking
