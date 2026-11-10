/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.GameTheory.DominatedStrategies

/-!
# Dominated-strategy reduction API checks

The worked example supplies an actual mixed equilibrium and a proof that exact reward matching
fails. These checks use its canonical development and pin the general assumptions separately:
ordinary reductions need only a preorder, while finite mixed reductions allow infinite retained
strategy carriers and require domination only at the incumbent for the pointwise theorem.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Probability

namespace MathEconLibTest.GameTheory.Reduction

open MathEconLibExamples.GameTheory.DominatedStrategies

example : game.IsFiniteMixedNash (fun i ↦ includeActions i (uniformProfile i)) :=
  full_equilibrium

example (σ : Bool → FinDist (Fin 2)) : reduced.IsNash σ ↔
    game.IsFiniteMixedNash (fun i ↦ includeActions i (σ i)) :=
  game.isNash_comapFiniteMixed_iff_of_dominated includeActions σ (pure_deviations_dominated σ)

example : ¬ ∃ f : GameMorphism reduced.nashProblem game.finiteMixedExtension.nashProblem,
    f.toFun = simulation.toFun := no_exact_morphism

section Api

variable {I V : Type*} {A B : I → Type*} [DecidableEq I]

example [Preorder V] (G : StrategicGame I A V) (f : ∀ i, B i → A i)
    (hdom : ∀ b i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) :
    GameSimulation (G.comapActions f).nashProblem G.nashProblem :=
  G.dominatedActionSimulation f hdom

example [Preorder V] (G : StrategicGame I A V) (f : ∀ i, B i → A i) (b : ∀ i, B i)
    (hdom : ∀ i a, ∃ b', G.payoff i (Function.update (fun j ↦ f j (b j)) i a) ≤
      (G.comapActions f).payoff i (Function.update b i b')) :
    (G.comapActions f).IsNash b ↔ G.IsNash (fun i ↦ f i (b i)) :=
  G.isNash_comapActions_iff_of_dominated f b hdom

example [Fintype I] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (G : StrategicGame I A ℝ) (f : ∀ i, B i → FinDist (A i))
    (hdom : ∀ b i a, ∃ b', G.finiteExpectedPayoff i
      (Function.update (fun j ↦ f j (b j)) i (FinDist.pure a)) ≤
        (G.finiteMixedExtension.comapActions f).payoff i (Function.update b i b')) :
    GameSimulation (G.finiteMixedExtension.comapActions f).nashProblem
      G.finiteMixedExtension.nashProblem := G.dominatedFiniteMixedSimulation f hdom

example [Fintype I] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [AddCommMonoid V] [Module ℝ V] (G : StrategicGame I A V)
    (σ : StrategicGame.FiniteMixedStrategy A) (i : I) (τ : FinDist (A i)) :
    G.finiteExpectedPayoff i (Function.update σ i τ) =
      τ.expect (fun a ↦ G.finiteExpectedPayoff i (Function.update σ i (FinDist.pure a))) :=
  G.finiteExpectedPayoff_update_eq_expect σ i τ

end Api

end MathEconLibTest.GameTheory.Reduction
