/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.ReductionSupport
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# Two dependent rounds of dominated-action elimination

The first restriction makes a further action dominated. Both proof routes
consume the same domination witnesses. Invalid premature restriction and a bad
retained row show why those witnesses are necessary.
-/

@[expose] public section

namespace MathEconLibTest.GameTheory.ChainedReductions

open MathEconLib.GameTheory
open MathEconLibTest.GameTheory.ReductionSupport

/-- The row action `false` dominates globally; the column action `false`
becomes dominant only after that row reduction. -/
def game : StrategicGame Bool (fun _ => Bool) ℝ where
  payoff
    | false, actions => if actions false then 1 else 2
    | true, actions =>
      if actions false then (if actions true then 3 else 0)
      else (if actions true then 0 else 2)

abbrev FirstAction : Bool → Type
  | false => Unit
  | true => Bool

def firstEmbedding : ∀ i, FirstAction i → Bool
  | false, _ => false
  | true, action => action

def firstRound : StrategicGame Bool FirstAction ℝ := game.comapActions firstEmbedding

def secondEmbedding : ∀ i, Unit → FirstAction i
  | false, _ => ()
  | true, _ => false

def secondRound : StrategicGame Bool (fun _ => Unit) ℝ :=
  firstRound.comapActions secondEmbedding

/-- These are the actual global coverage witnesses used by both routes. -/
theorem first_domination (profile : ∀ i, FirstAction i) (i : Bool) (action : Bool) :
    ∃ replacement : FirstAction i,
      game.payoff i (Function.update (fun j => firstEmbedding j (profile j)) i action) ≤
        firstRound.payoff i (Function.update profile i replacement) := by
  cases i
  · refine ⟨(), ?_⟩
    cases action <;>
      norm_num [game, firstRound, StrategicGame.comapActions, firstEmbedding]
  · refine ⟨action, ?_⟩
    cases action <;>
      norm_num [game, firstRound, StrategicGame.comapActions, firstEmbedding]

theorem second_domination (profile : Bool → Unit) (i : Bool) (action : FirstAction i) :
    ∃ replacement : Unit,
      firstRound.payoff i
          (Function.update (fun j => secondEmbedding j (profile j)) i action) ≤
        secondRound.payoff i (Function.update profile i replacement) := by
  cases i
  · cases action
    refine ⟨(), ?_⟩
    norm_num [game, firstRound, secondRound, StrategicGame.comapActions,
      firstEmbedding, secondEmbedding]
  · refine ⟨(), ?_⟩
    cases action <;>
      norm_num [game, firstRound, secondRound, StrategicGame.comapActions,
        firstEmbedding, secondEmbedding]

/-- The second elimination would be invalid before restricting the row. -/
theorem column_false_not_globally_dominant :
    ¬ ∀ profile : Bool → Bool,
      game.payoff true (Function.update profile true true) ≤
        game.payoff true (Function.update profile true false) := by
  intro dominated
  have impossible := dominated (fun _ => true)
  norm_num [game] at impossible

def firstSimulation : GameSimulation firstRound.nashProblem game.nashProblem :=
  dominatedActionSimulation game firstEmbedding first_domination

def secondSimulation : GameSimulation secondRound.nashProblem firstRound.nashProblem :=
  dominatedActionSimulation firstRound secondEmbedding second_domination

def finalProfile : Bool → Unit := fun _ => ()

def middleProfile : ∀ i, FirstAction i := fun i => secondEmbedding i (finalProfile i)

def finalImage : Bool → Bool := fun i => firstEmbedding i (middleProfile i)

theorem finalImage_false (i : Bool) : finalImage i = false := by cases i <;> rfl

private theorem singleton_actions_isNash
    (G : StrategicGame Bool (fun _ => Unit) ℝ) : G.IsNash finalProfile := by
  rw [StrategicGame.isNash_iff]
  intro i action
  cases action
  have unchanged : Function.update finalProfile i () = finalProfile := by
    funext j
    cases i <;> cases j <;> rfl
  simpa only [unchanged] using (le_refl (G.payoff i finalProfile))

theorem final_isNash : secondRound.IsNash finalProfile :=
  singleton_actions_isNash secondRound

/-- One composite certificate preserves equilibrium along both reductions. -/
theorem record_equivalence : secondRound.IsNash finalProfile ↔ game.IsNash finalImage :=
  ⟨(firstSimulation.comp secondSimulation).transport,
    fun equilibrium => (equilibrium.comapActions firstEmbedding).comapActions secondEmbedding⟩

/-- Both direct equivalences receive the same global witnesses, specialized
at the actual profiles of the two rounds. -/
theorem direct_equivalence : secondRound.IsNash finalProfile ↔ game.IsNash finalImage :=
  (isNash_comapActions_iff_of_dominated firstRound secondEmbedding finalProfile
    (second_domination finalProfile)).trans
    (isNash_comapActions_iff_of_dominated game firstEmbedding middleProfile
      (first_domination middleProfile))

theorem original_isNash_by_record : game.IsNash finalImage := record_equivalence.mp final_isNash

theorem original_isNash_by_direct : game.IsNash finalImage := direct_equivalence.mp final_isNash

/-- Retaining the inferior row action produces another singleton final game,
but its equilibrium cannot be transported to the original game. -/
def badFirstEmbedding : ∀ i, FirstAction i → Bool
  | false, _ => true
  | true, action => action

def badSecondEmbedding : ∀ i, Unit → FirstAction i
  | false, _ => ()
  | true, _ => true

def badFinalGame : StrategicGame Bool (fun _ => Unit) ℝ :=
  (game.comapActions badFirstEmbedding).comapActions badSecondEmbedding

def badImage : Bool → Bool :=
  fun i => badFirstEmbedding i (badSecondEmbedding i (finalProfile i))

theorem bad_final_isNash : badFinalGame.IsNash finalProfile :=
  singleton_actions_isNash badFinalGame

/-- The bad first restriction cannot supply the domination hypothesis used by either route. -/
theorem bad_first_not_domination :
    ¬ ∀ (profile : ∀ i, FirstAction i) (i : Bool) (action : Bool),
      ∃ replacement : FirstAction i,
        game.payoff i
            (Function.update (fun j => badFirstEmbedding j (profile j)) i action) ≤
          (game.comapActions badFirstEmbedding).payoff i
            (Function.update profile i replacement) := by
  intro dominated
  obtain ⟨replacement, bound⟩ := dominated middleProfile false false
  cases replacement
  norm_num [game, StrategicGame.comapActions, badFirstEmbedding] at bound

theorem bad_image_not_isNash : ¬ game.IsNash badImage := by
  intro equilibrium
  have impossible := (StrategicGame.isNash_iff game badImage).mp equilibrium false false
  norm_num [game, badImage, badFirstEmbedding, badSecondEmbedding] at impossible

end MathEconLibTest.GameTheory.ChainedReductions
