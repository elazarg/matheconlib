/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Logic.Relation

/-!
# Witness-preserving reductions of obstructions

States and obstruction proposals have separate types. A reduction lifts each
target obstruction to a source obstruction and records a state-dependent
relation between their witnesses. Composition retains an actual intermediate
obstruction as well as both provenance relations. Candidate validity is separate;
clients can enforce it through certified state types when needed.
-/

@[expose] public section

namespace MathEconLib

universe u v w x y z u' v'

/-- A state translation that lifts obstructions with related source witnesses. -/
structure WitnessLift {C : Type u} {D : Type v} {P : Type w} {Q : Type x}
    (source : C → P → Prop) (target : D → Q → Prop) where
  state : C → D
  related : C → Q → P → Prop
  covers : ∀ c q, target (state c) q → ∃ p, related c q p ∧ source c p

namespace WitnessLift

variable {C : Type u} {D : Type v} {E : Type y}
  {P : Type w} {Q : Type x} {R : Type z}
  {source : C → P → Prop} {middle : D → Q → Prop} {target : E → R → Prop}

/-- Absence of source obstructions implies absence of target obstructions. -/
theorem transport (f : WitnessLift source middle) {c : C} (unblocked : ∀ p, ¬ source c p) :
    ∀ q, ¬ middle (f.state c) q := by
  intro q blocks
  obtain ⟨p, _, original⟩ := f.covers c q blocks
  exact unblocked p original

/-- Compose translations while retaining an actual intermediate obstruction. -/
def comp (g : WitnessLift middle target) (f : WitnessLift source middle) :
    WitnessLift source target where
  state := g.state ∘ f.state
  related c r p :=
    ∃ q, middle (f.state c) q ∧ g.related (f.state c) r q ∧ f.related c q p
  covers c r blocks := by
    obtain ⟨q, relatedQ, middleBlock⟩ := g.covers (f.state c) r blocks
    obtain ⟨p, relatedP, sourceBlock⟩ := f.covers c q middleBlock
    exact ⟨p, ⟨q, middleBlock, relatedQ, relatedP⟩, sourceBlock⟩

/-- The composite follows the two supplied state translations. -/
theorem comp_state (g : WitnessLift middle target) (f : WitnessLift source middle) :
    (g.comp f).state = g.state ∘ f.state := rfl

/-- Reassociation retains the same two actual intermediate obstructions and relations. -/
theorem comp_related_assoc {F : Type u'} {Z : Type v'} {final : F → Z → Prop}
    (h : WitnessLift target final) (g : WitnessLift middle target)
    (f : WitnessLift source middle) (c : C) (r : Z) (p : P) :
    ((h.comp g).comp f).related c r p ↔ (h.comp (g.comp f)).related c r p := by
  constructor
  · rintro ⟨q, middleBlock, ⟨t, targetBlock, relatedH, relatedG⟩, relatedF⟩
    exact ⟨t, targetBlock, relatedH, q, middleBlock, relatedG, relatedF⟩
  · rintro ⟨t, targetBlock, relatedH, q, middleBlock, relatedG, relatedF⟩
    exact ⟨q, middleBlock, ⟨t, targetBlock, relatedH, relatedG⟩, relatedF⟩

end WitnessLift
end MathEconLib
