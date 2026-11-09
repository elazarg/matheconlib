/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Problem
public import Mathlib.Order.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Equilibrium transport by deviation domination

A simulation bounds every target deviation by an admissible source deviation.
The translated incumbent may have a larger value. Exact morphisms are a special
case. Scalar utility evaluation is an application of this ordered-value contract.
Reflection requires a separate comorphism; preservation alone does not imply it.
-/

@[expose] public section

namespace MathEconLib.GameTheory

universe u v w x y z r

/-- A state translation preserving validity and bounding each target deviation
by a source deviation, while weakly increasing incumbent values. -/
structure GameSimulation {V : Type r} [LE V] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem T J V) where
  /-- Translate source candidates into target candidates. -/
  toFun : S → T
  /-- The source deviator representing each target deviator. -/
  deviatorMap : J → I
  /-- Translation weakly increases the incumbent's value. -/
  value_le : ∀ j s, P.value (deviatorMap j) s ≤ Q.value j (toFun s)
  /-- Every target deviation is bounded by one admissible source deviation. -/
  deviation_dominated : ∀ j s t, Q.deviation j (toFun s) t →
    ∃ s', P.deviation (deviatorMap j) s s' ∧
      Q.value j t ≤ P.value (deviatorMap j) s'
  /-- Valid source candidates have valid images. -/
  valid_preserves : ∀ s, P.valid s → Q.valid (toFun s)

namespace EquilibriumProblem

variable {V : Type r} [Preorder V] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}

/-- Pointwise domination transports optimality without requiring a bundled map
or any hypothesis about candidates other than the one under consideration. -/
theorem IsDeviationOptimal.of_dominated_deviations {s : S} {t : T}
    (h : P.IsDeviationOptimal s) (g : J → I)
    (hbase : ∀ j, P.value (g j) s ≤ Q.value j t)
    (hdev : ∀ j t', Q.deviation j t t' →
      ∃ s', P.deviation (g j) s s' ∧ Q.value j t' ≤ P.value (g j) s') :
    Q.IsDeviationOptimal t := by
  intro j t' ht'
  obtain ⟨s', hs', hbound⟩ := hdev j t' ht'
  exact hbound.trans ((h (g j) s' hs').trans (hbase j))

end EquilibriumProblem

namespace GameSimulation

section Extensionality

variable {V : Type r} [LE V] {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}

/-- Simulation certificates with the same maps are equal by proof irrelevance. -/
@[ext] theorem ext {f g : GameSimulation P Q} (hf : f.toFun = g.toFun)
    (hg : f.deviatorMap = g.deviatorMap) : f = g := by
  cases f
  cases g
  cases hf
  cases hg
  rfl

end Extensionality

variable {V : Type r} [Preorder V] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    {R : EquilibriumProblem U K V}

/-- Domination transports deviation optimality without a validity assumption. -/
theorem transport_isDeviationOptimal (f : GameSimulation P Q) {s : S}
    (h : P.IsDeviationOptimal s) : Q.IsDeviationOptimal (f.toFun s) :=
  h.of_dominated_deviations f.deviatorMap (fun j ↦ f.value_le j s)
    (fun j t ↦ f.deviation_dominated j s t)

/-- A simulation sends equilibria to equilibria. -/
theorem transport (f : GameSimulation P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) :=
  ⟨f.valid_preserves s h.valid, f.transport_isDeviationOptimal h.deviation_le⟩

/-- The identity simulation. -/
def id (P : EquilibriumProblem S I V) : GameSimulation P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  value_le _ _ := le_rfl
  deviation_dominated _ _ t ht := ⟨t, ht, le_rfl⟩
  valid_preserves _ h := h

/-- Simulations compose by composing maps and chaining the deviation bounds. -/
def comp (g : GameSimulation Q R) (f : GameSimulation P Q) : GameSimulation P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := f.deviatorMap ∘ g.deviatorMap
  value_le k s := (f.value_le (g.deviatorMap k) s).trans (g.value_le k (f.toFun s))
  deviation_dominated k s t ht := by
    obtain ⟨q, hq, hb⟩ := g.deviation_dominated k (f.toFun s) t ht
    obtain ⟨p, hp, hc⟩ := f.deviation_dominated (g.deviatorMap k) s q hq
    exact ⟨p, hp, hb.trans hc⟩
  valid_preserves s hs := g.valid_preserves (f.toFun s) (f.valid_preserves s hs)

@[simp] theorem id_comp (f : GameSimulation P Q) : (id Q).comp f = f := by
  ext <;> rfl

@[simp] theorem comp_id (f : GameSimulation P Q) : f.comp (id P) = f := by
  ext <;> rfl

theorem comp_assoc {A B : Type*} {W : EquilibriumProblem A B V}
    (h : GameSimulation R W) (g : GameSimulation Q R) (f : GameSimulation P Q) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  ext <;> rfl

/-- A separate reflection contract on the same state map gives an iff. -/
theorem isEquilibrium_iff (f : GameSimulation P Q) (g : GameComorphism P Q)
    (hmap : g.toFun = f.toFun) (s : S) :
    Q.IsEquilibrium (f.toFun s) ↔ P.IsEquilibrium s :=
  ⟨fun h ↦ g.pullback (hmap ▸ h), f.transport⟩

/-- Additive slack transports unchanged whenever addition is monotone on the
right. This states the inequalities without introducing another equilibrium predicate. -/
theorem transport_le_add [Add V] [AddRightMono V] (f : GameSimulation P Q) (ε : V) {s : S}
    (h : ∀ i s', P.deviation i s s' → P.value i s' ≤ P.value i s + ε) :
    ∀ j t, Q.deviation j (f.toFun s) t → Q.value j t ≤ Q.value j (f.toFun s) + ε := by
  intro j t ht
  obtain ⟨s', hs', hbound⟩ := f.deviation_dominated j s t ht
  exact hbound.trans ((h (f.deviatorMap j) s' hs').trans (add_le_add_left (f.value_le j s) ε))

end GameSimulation

namespace GameMorphism

variable {V : Type r} [Preorder V] {S : Type u} {I : Type v}
    {T : Type w} {J : Type x} {U : Type y} {K : Type z}
    {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J V}
    {R : EquilibriumProblem U K V}

/-- Exact deviation lifting is a special case of deviation domination. -/
def toSimulation (f : GameMorphism P Q) : GameSimulation P Q where
  toFun := f.toFun
  deviatorMap := f.deviatorMap
  value_le j s := (f.value_eq j s).symm.le
  deviation_dominated j s t ht := by
    obtain ⟨s', hs', rfl⟩ := f.deviation_lifts j s t ht
    exact ⟨s', hs', (f.value_eq j s').le⟩
  valid_preserves := f.valid_preserves

@[simp] theorem toSimulation_id (P : EquilibriumProblem S I V) :
    (id P).toSimulation = GameSimulation.id P := by
  ext <;> rfl

@[simp] theorem toSimulation_comp (g : GameMorphism Q R) (f : GameMorphism P Q) :
    (g.comp f).toSimulation = g.toSimulation.comp f.toSimulation := by
  ext <;> rfl

end GameMorphism

end MathEconLib.GameTheory
