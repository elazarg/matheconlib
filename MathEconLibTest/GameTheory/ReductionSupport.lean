/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Equilibrium transport and dominated-action reductions

A simulation preserves candidate validity and bounds every target deviation by a source
one after monotone value recoding. Simulations compose by chaining these bounds.
The pointwise reduction theorem proves the same included-profile equivalence directly.
-/

@[expose] public section

namespace MathEconLibTest.GameTheory.ReductionSupport

open MathEconLib.GameTheory

universe u v w x y z

/-- A state translation with playerwise monotone recoding and dominated deviations. -/
structure GameSimulation {V W : Type*} [Preorder V] [Preorder W]
    {S : Type u} {I : Type v} {T : Type w} {J : Type x}
    (P : EquilibriumProblem S I V) (Q : EquilibriumProblem T J W) where
  toFun : S → T
  deviatorMap : J → I
  valueMap : J → V →o W
  value_le : ∀ j s, valueMap j (P.value (deviatorMap j) s) ≤ Q.value j (toFun s)
  deviation_dominated : ∀ j s t, Q.deviation j (toFun s) t →
    ∃ s', P.deviation (deviatorMap j) s s' ∧
      Q.value j t ≤ valueMap j (P.value (deviatorMap j) s')
  valid_preserves : ∀ s, P.valid s → Q.valid (toFun s)

namespace GameSimulation

variable {V W X : Type*} [Preorder V] [Preorder W] [Preorder X]
  {S : Type u} {I : Type v} {T : Type w} {J : Type x} {U : Type y} {K : Type z}
  {P : EquilibriumProblem S I V} {Q : EquilibriumProblem T J W}
  {R : EquilibriumProblem U K X}

/-- A simulation sends valid equilibria to valid equilibria. -/
theorem transport (f : GameSimulation P Q) {s : S} (h : P.IsEquilibrium s) :
    Q.IsEquilibrium (f.toFun s) := by
  refine ⟨f.valid_preserves s h.valid, ?_⟩
  intro j t ht
  obtain ⟨s', hs', bound⟩ := f.deviation_dominated j s t ht
  exact bound.trans (((f.valueMap j).monotone
    (h.deviation_le (f.deviatorMap j) s' hs')).trans (f.value_le j s))

/-- The identity keeps all state, judge, reward and validity information. -/
def id (P : EquilibriumProblem S I V) : GameSimulation P P where
  toFun := _root_.id
  deviatorMap := _root_.id
  valueMap _ := OrderHom.id
  value_le _ _ := le_rfl
  deviation_dominated _ _ t ht := ⟨t, ht, le_rfl⟩
  valid_preserves _ h := h

/-- Compose full simulation certificates, including their deviation witnesses. -/
def comp (g : GameSimulation Q R) (f : GameSimulation P Q) : GameSimulation P R where
  toFun := g.toFun ∘ f.toFun
  deviatorMap := f.deviatorMap ∘ g.deviatorMap
  valueMap k := (g.valueMap k).comp (f.valueMap (g.deviatorMap k))
  value_le k s := ((g.valueMap k).monotone (f.value_le (g.deviatorMap k) s)).trans
    (g.value_le k (f.toFun s))
  deviation_dominated k s t ht := by
    obtain ⟨q, hq, hb⟩ := g.deviation_dominated k (f.toFun s) t ht
    obtain ⟨p, hp, hc⟩ := f.deviation_dominated (g.deviatorMap k) s q hq
    exact ⟨p, hp, hb.trans ((g.valueMap k).monotone hc)⟩
  valid_preserves s hs := g.valid_preserves (f.toFun s) (f.valid_preserves s hs)

end GameSimulation

variable {I V : Type*} {A B : I → Type*} [DecidableEq I]

/-- Every full deviation is bounded by a retained action at every retained profile. -/
def dominatedActionSimulation [Preorder V] (G : StrategicGame I A V)
    (f : ∀ i, B i → A i)
    (hdom : ∀ b i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) :
    GameSimulation (G.comapActions f).nashProblem G.nashProblem where
  toFun b j := f j (b j)
  deviatorMap := _root_.id
  valueMap _ := OrderHom.id
  value_le _ _ := le_rfl
  deviation_dominated i b _ ht := by
    obtain ⟨a, rfl⟩ := ht
    obtain ⟨b', hb'⟩ := hdom b i a
    exact ⟨Function.update b i b', ⟨b', rfl⟩, hb'⟩
  valid_preserves _ _ := trivial

/-- Pointwise domination gives equivalence at the included profile, without a certificate. -/
theorem isNash_comapActions_iff_of_dominated [Preorder V] (G : StrategicGame I A V)
    (f : ∀ i, B i → A i) (b : ∀ i, B i)
    (hdom : ∀ i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) :
    (G.comapActions f).IsNash b ↔ G.IsNash (fun i ↦ f i (b i)) := by
  constructor
  · intro h
    rw [StrategicGame.isNash_iff] at h ⊢
    intro i a
    obtain ⟨b', bound⟩ := hdom i a
    exact bound.trans (h i b')
  · intro h
    exact h.comapActions f

end MathEconLibTest.GameTheory.ReductionSupport
