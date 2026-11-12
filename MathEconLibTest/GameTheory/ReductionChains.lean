/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.ReductionSupport

/-!
# Finite chains of equilibrium transports

Per-round implications and equivalences compose directly. Full simulation
certificates also compose, retaining their value maps and deviation witnesses.
The two constructions use the same composite state map.
-/

@[expose] public section

namespace MathEconLibTest.GameTheory.ReductionSupport

open MathEconLib.GameTheory

universe u v w

/-- Execute the state translations from a reduced stage back to the initial stage. -/
def chainMap {S : ℕ → Type u} (step : ∀ n, S (n + 1) → S n) : ∀ n, S n → S 0
  | 0 => id
  | n + 1 => chainMap step n ∘ step n

/-- Local preservation suffices to transport a verdict through any finite chain. -/
theorem transport_chain {S : ℕ → Type u} (holds : ∀ n, S n → Prop)
    (step : ∀ n, S (n + 1) → S n)
    (preserves : ∀ n s, holds (n + 1) s → holds n (step n s)) :
    ∀ n s, holds n s → holds 0 (chainMap step n s)
  | 0, _, h => h
  | n + 1, s, h => transport_chain holds step preserves n (step n s) (preserves n s h)

/-- Local equivalences compose without constructing a simulation certificate. -/
theorem iff_chain {S : ℕ → Type u} (holds : ∀ n, S n → Prop)
    (step : ∀ n, S (n + 1) → S n)
    (same : ∀ n s, holds (n + 1) s ↔ holds n (step n s)) :
    ∀ n s, holds n s ↔ holds 0 (chainMap step n s)
  | 0, _ => Iff.rfl
  | n + 1, s => (same n s).trans (iff_chain holds step same n (step n s))

namespace GameSimulation

variable {V : Type w} [Preorder V] {S : ℕ → Type u} {I : ℕ → Type v}

/-- Compose full certificates over arbitrary finite stages, with changing state and judge types. -/
def chain (P : ∀ n, EquilibriumProblem (S n) (I n) V)
    (step : ∀ n, GameSimulation (P (n + 1)) (P n)) :
    ∀ n, GameSimulation (P n) (P 0)
  | 0 => id (P 0)
  | n + 1 => (chain P step n).comp (step n)

/-- Certificate composition and direct verdict composition have exactly the same state map. -/
theorem chain_toFun (P : ∀ n, EquilibriumProblem (S n) (I n) V)
    (step : ∀ n, GameSimulation (P (n + 1)) (P n)) :
    ∀ n s, (chain P step n).toFun s = chainMap (fun n => (step n).toFun) n s
  | 0, _ => rfl
  | n + 1, s => chain_toFun P step n ((step n).toFun s)

end GameSimulation

end MathEconLibTest.GameTheory.ReductionSupport
