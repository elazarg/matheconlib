/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Filter.Extr

/-!
# Guarded optimality on a menu

The chosen alternative and all offered alternatives must lie in the evaluation
domain. A comparison is written alternative first, chosen second. Domain
membership, menu membership, and the comparison are independent arguments.
The chosen alternative remains guarded when the menu is empty.
-/

@[expose] public section

namespace MathEconLib

universe uα uβ us ut

/-- The chosen alternative is evaluable, and every offered alternative is
evaluable and weakly below it under the supplied comparison. No relation laws
or membership of the chosen alternative in the menu are implied. -/
def IsOptimalOn {α : Type uα} (ok : α → Prop) (R : α → α → Prop)
    (S : Set α) (chosen : α) : Prop :=
  ok chosen ∧ ∀ alternative ∈ S, ok alternative ∧ R alternative chosen

/-- Guarded optimality transports when the chosen guard transfers and every
target alternative has a covering source alternative that transports both its
guard and its comparison. The source and target menus need not be bijective. -/
theorem IsOptimalOn.of_coverage
    {Source : Type us} {Target : Type ut}
    {sourceOk : Source → Prop} {targetOk : Target → Prop}
    {sourceR : Source → Source → Prop} {targetR : Target → Target → Prop}
    {sourceMenu : Set Source} {targetMenu : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : IsOptimalOn sourceOk sourceR sourceMenu chosen)
    (base : sourceOk chosen → targetOk compiled)
    (coverage : ∀ alternative ∈ targetMenu, ∃ original ∈ sourceMenu,
      (sourceOk original → targetOk alternative) ∧
        (sourceR original chosen → targetR alternative compiled)) :
    IsOptimalOn targetOk targetR targetMenu compiled := by
  refine ⟨base optimal.1, ?_⟩
  intro alternative offered
  obtain ⟨original, covered, guard, comparison⟩ := coverage alternative offered
  have originalOptimal := optimal.2 original covered
  exact ⟨guard originalOptimal.1, comparison originalOptimal.2⟩

/-- With no evaluation-domain restriction, optimality is the bare rooted
comparison against each offered alternative. -/
theorem isOptimalOn_true_iff {α : Type uα} (R : α → α → Prop)
    (S : Set α) (chosen : α) :
    IsOptimalOn (fun _ => True) R S chosen ↔ ∀ alternative ∈ S, R alternative chosen := by
  constructor
  · exact fun optimal alternative offered => (optimal.2 alternative offered).2
  · exact fun comparisons => ⟨trivial, fun alternative offered =>
      ⟨trivial, comparisons alternative offered⟩⟩

/-- Taking evaluability to mean menu membership gives feasible greatest
choice. This adds the chosen alternative's feasibility explicitly. -/
theorem isOptimalOn_mem_iff {α : Type uα} (R : α → α → Prop)
    (S : Set α) (chosen : α) :
    IsOptimalOn (fun alternative => alternative ∈ S) R S chosen ↔
      chosen ∈ S ∧ ∀ alternative ∈ S, R alternative chosen := by
  constructor
  · exact fun optimal => ⟨optimal.1, fun alternative offered =>
      (optimal.2 alternative offered).2⟩
  · exact fun ⟨member, comparisons⟩ => ⟨member, fun alternative offered =>
      ⟨offered, comparisons alternative offered⟩⟩

/-- Mathlib score maximization has no chosen-menu membership requirement.
This is an equivalence to its standard predicate, not a second definition. -/
theorem isOptimalOn_score_iff {α : Type uα} {β : Type uβ} [Preorder β]
    (score : α → β) (S : Set α) (chosen : α) :
    IsOptimalOn (fun _ => True) (fun alternative incumbent => score alternative ≤ score incumbent)
      S chosen ↔ IsMaxOn score S chosen :=
  (isOptimalOn_true_iff _ S chosen).trans isMaxOn_iff.symm

/-- A score maximizer with explicit feasibility specializes the membership
guard while retaining Mathlib's own maximization predicate. -/
theorem isOptimalOn_mem_score_iff {α : Type uα} {β : Type uβ} [Preorder β]
    (score : α → β) (S : Set α) (chosen : α) :
    IsOptimalOn (fun alternative => alternative ∈ S)
      (fun alternative incumbent => score alternative ≤ score incumbent) S chosen ↔
      chosen ∈ S ∧ IsMaxOn score S chosen := by
  rw [isOptimalOn_mem_iff, isMaxOn_iff]

/-- An empty menu does not discharge the chosen alternative's guard. -/
theorem isOptimalOn_empty_iff {α : Type uα} (ok : α → Prop) (R : α → α → Prop)
    (chosen : α) : IsOptimalOn ok R ∅ chosen ↔ ok chosen := by
  constructor
  · exact fun optimal => optimal.1
  · exact fun guard => ⟨guard, fun _ impossible => False.elim impossible⟩

end MathEconLib
