/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Logic.Relation

/-!
# Witness-preserving reductions of obstructions

States and obstruction proposals have separate types. A reduction lifts a
target obstruction to a source obstruction and retains a relation between the
witnesses. Composition retains that provenance as an existential relation.
Admissibility of states is a separate condition, not a condition on witnesses.
-/

@[expose] public section

namespace MathEconLibTest.AbstractionExperiments

universe u v w x y z

/-- A state map that lifts obstructions while preserving witness provenance. -/
structure WitnessLift {C : Type u} {D : Type v} {P : Type w} {Q : Type x}
    (source : C → P → Prop) (target : D → Q → Prop) where
  state : C → D
  related : C → Q → P → Prop
  covers : ∀ c q, target (state c) q → ∃ p, related c q p ∧ source c p

namespace WitnessLift

variable {C : Type u} {D : Type v} {E : Type y}
  {P : Type w} {Q : Type x} {R : Type z}
  {source : C → P → Prop} {middle : D → Q → Prop} {target : E → R → Prop}

/-- Lifting positive obstruction witnesses transports absence of obstructions. -/
theorem transport (f : WitnessLift source middle) {c : C} (h : ∀ p, ¬ source c p) :
    ∀ q, ¬ middle (f.state c) q := by
  intro q blocks
  obtain ⟨p, _, original⟩ := f.covers c q blocks
  exact h p original

/-- Compose state maps and retain the relation through the intermediate witness. -/
def comp (g : WitnessLift middle target) (f : WitnessLift source middle) :
    WitnessLift source target where
  state := g.state ∘ f.state
  related c r p := ∃ q, g.related (f.state c) r q ∧ f.related c q p
  covers c r blocks := by
    obtain ⟨q, relatedQ, middleBlock⟩ := g.covers (f.state c) r blocks
    obtain ⟨p, relatedP, sourceBlock⟩ := f.covers c q middleBlock
    exact ⟨p, ⟨q, relatedQ, relatedP⟩, sourceBlock⟩

end WitnessLift

end MathEconLibTest.AbstractionExperiments
