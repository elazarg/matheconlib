/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.Basic
public import MathEconLib.Mechanism.Auctions.AllPurchase.WithPrice
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Comap
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The original action domain changes actual all-purchase Bayesian incentives

At price four, zero private values and zero opponents' bids give net payment
`b²+b`. A negative real bid earns a positive transfer, excluding zero bidding
from native Bayesian equilibrium under a Dirac prior of mass one. Restricting
exactly the same mechanism through nonnegative-action inclusion gives native
Bayesian equilibrium against every measurable restricted deviation under the
same prior. Outcomes and transfers are inherited by `Mechanism.comap`.

The restricted object is a general mechanism and its induced Bayesian game.
The scalar auction and all-purchase specification retain their original real
bid carriers; no automatic transfer of that entire analysis is asserted.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.Mechanism.AllPurchaseActionDomain

open MeasureTheory ProbabilityTheory Set
open MathEconLib MathEconLib.GameTheory MathEconLib.Mechanism
open scoped NNReal

abbrev realMechanism := MathEconLib.Examples.AllPurchase.spec.rulesAtPrice 4

abbrev environment := Auction.valuationEnvironment 2

abbrev realGame := realMechanism.inducedBayesianGame environment

def zeroTypes : Fin 2 → ℝ := fun _ => 0

def prior : Measure (Fin 2 → ℝ) := Measure.dirac zeroTypes

instance : IsProbabilityMeasure prior := inferInstanceAs (IsProbabilityMeasure (Measure.dirac _))

/-- All mass lies at the true profile used by the incentive comparison. -/
theorem prior_atom : prior {zeroTypes} = 1 := by simp [prior]

def inclusion (_ : Fin 2) : ℝ≥0 → ℝ := fun bid => bid

abbrev restrictedMechanism := realMechanism.comap inclusion

abbrev restrictedGame := restrictedMechanism.inducedBayesianGame environment

theorem restricted_mechanism_eq : restrictedMechanism = realMechanism.comap inclusion := rfl

theorem restricted_game_eq : restrictedGame = realGame.comapActions inclusion := rfl

/-- The restriction inherits the original signed transfers, evaluated on included actions. -/
theorem restricted_transfer_eq (i : Fin 2) (bids : Fin 2 → ℝ≥0) :
    restrictedMechanism.transfer i bids =
      realMechanism.transfer i (fun j => (bids j : ℝ)) := rfl

/-- The actual original net payment against zero opponents is quadratic. -/
theorem payment_update_zero (i : Fin 2) (bid : ℝ) :
    realMechanism.payment i (Function.update zeroTypes i bid) = bid ^ 2 + bid := by
  change -(-((4 - (3 - ∑ j, Function.update zeroTypes i bid j)) *
    Function.update zeroTypes i bid i)) = _
  simp only [neg_neg, Function.update_self]
  simp [zeroTypes, Finset.sum_update_univ]
  ring

/-- At the atom, the private-value term vanishes; signed transfers remain unchanged. -/
theorem real_payoff_zero (i : Fin 2) (bids : Fin 2 → ℝ) :
    realGame.payoff i bids zeroTypes = -((1 + ∑ j, bids j) * bids i) := by
  change (0 : ℝ) * realMechanism.outcome bids i + realMechanism.transfer i bids = _
  simp only [zero_mul, zero_add]
  change -((4 - (3 - ∑ j, bids j)) * bids i) = _
  ring

theorem restricted_payoff_zero (i : Fin 2) (bids : Fin 2 → ℝ≥0) :
    restrictedGame.payoff i bids zeroTypes =
      -((1 + ∑ j, (bids j : ℝ)) * (bids i : ℝ)) :=
  real_payoff_zero i (fun j => (bids j : ℝ))

def zeroReal : realGame.Strategy := fun _ => ⟨fun _ => 0, measurable_const⟩

def zeroRestricted : restrictedGame.Strategy := fun _ => ⟨fun _ => 0, measurable_const⟩

def negativeDeviation : realGame.Strategy :=
  realGame.replace zeroReal 0 ⟨fun _ => -(1 / 2 : ℝ), measurable_const⟩

/-- Dirac-supported real payoffs are integrable for every original measurable strategy. -/
theorem real_integrable (strategy : realGame.Strategy) :
    realGame.IncumbentPayoffsIntegrable prior strategy := by
  intro i
  exact integrable_dirac (by simp)

theorem restricted_integrable (strategy : restrictedGame.Strategy) :
    restrictedGame.IncumbentPayoffsIntegrable prior strategy := by
  intro i
  exact integrable_dirac (by simp)

theorem zeroReal_payoff (i : Fin 2) : realGame.exAntePayoff prior i zeroReal = 0 := by
  simp only [BayesianGame.exAntePayoff, prior, integral_dirac, real_payoff_zero]
  simp [BayesianGame.measurableActionProfile, zeroReal]

theorem negativeDeviation_payoff : realGame.exAntePayoff prior 0 negativeDeviation = 1 / 4 := by
  simp only [BayesianGame.exAntePayoff, prior, integral_dirac, real_payoff_zero]
  rw [Fin.sum_univ_two]
  change -((1 + (-(1 / 2 : ℝ) + 0)) * -(1 / 2 : ℝ)) = 1 / 4
  norm_num

/-- The negative-bid gain occurs at an actual prior atom and is an admitted native deviation. -/
theorem zeroReal_not_isBNE : ¬ realGame.IsBNE prior zeroReal := by
  intro equilibrium
  have opponents : ∀ j, j ≠ 0 → negativeDeviation j = zeroReal j := by
    intro j different
    exact realGame.replace_of_ne zeroReal 0 _ different
  have comparison : realGame.exAntePayoff prior 0 negativeDeviation ≤
      realGame.exAntePayoff prior 0 zeroReal :=
    equilibrium.deviation_le 0 negativeDeviation ⟨opponents, real_integrable negativeDeviation 0⟩
  rw [negativeDeviation_payoff, zeroReal_payoff] at comparison
  norm_num at comparison

theorem zeroRestricted_payoff (i : Fin 2) :
    restrictedGame.exAntePayoff prior i zeroRestricted = 0 := by
  simp only [BayesianGame.exAntePayoff, prior, integral_dirac, restricted_payoff_zero]
  simp [BayesianGame.measurableActionProfile, zeroRestricted]

/-- Every restricted profile has nonpositive utility at the actual zero-value atom. -/
theorem restricted_payoff_nonpos (i : Fin 2) (bids : Fin 2 → ℝ≥0) :
    restrictedGame.payoff i bids zeroTypes ≤ 0 := by
  rw [restricted_payoff_zero]
  apply neg_nonpos.mpr
  apply mul_nonneg
  · have total : 0 ≤ ∑ j : Fin 2, (bids j : ℝ) :=
      Finset.sum_nonneg fun j _ => (bids j).property
    linarith
  · exact (bids i).property

/-- The exact same mechanism restricted to nonnegative bids admits the zero native BNE. -/
theorem zeroRestricted_isBNE : restrictedGame.IsBNE prior zeroRestricted := by
  rw [BayesianGame.isBNE_iff]
  refine ⟨?_, restricted_integrable zeroRestricted⟩
  intro i alternative _opponents _integrable
  rw [zeroRestricted_payoff]
  simp only [BayesianGame.exAntePayoff, prior, integral_dirac]
  exact restricted_payoff_nonpos i _

/-- The two incumbent strategies prescribe the same included actions at every type. -/
theorem zeroStrategies_agree :
    BayesianGame.Strategy.mapActions realGame
        (fun i => ⟨inclusion i, measurable_subtype_coe⟩) zeroRestricted = zeroReal := rfl
/-- The inclusion has the native direction: original BNE pulls back to restricted BNE. -/
def inclusionComorphism :
    GameComorphism (restrictedGame.bneProblem prior) (realGame.bneProblem prior) :=
  realGame.comapActionsComorphism prior
    (fun i => ⟨inclusion i, measurable_subtype_coe⟩)

end MathEconLibTest.Mechanism.AllPurchaseActionDomain
