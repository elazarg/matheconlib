/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Mixture
public import MathEconLib.GameTheory.Strategic.Outcome

/-!
# Expected Nash transport for stochastic outcome games

A utility-independent simulation of unilateral deviations preserves the expected
Nash problem for every integrable ordered utility evaluation. Outcome laws and
values come from `OutcomeGame.toKernel` and `PayoffStructure.expected`; the
expected-utility construction supplies the integrability restrictions.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace MathEconLib.GameTheory.MixtureSimulation

variable {I J O V : Type*} {A : I → Type*} {B : J → Type*}
    [DecidableEq I] [DecidableEq J] [∀ i, MeasurableSpace (A i)]
    [∀ j, MeasurableSpace (B j)] [MeasurableSpace O]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [PartialOrder V] [IsOrderedAddMonoid V] [IsOrderedModule ℝ V] [ClosedIciTopology V]
    {G : OutcomeGame I A (ProbabilityMeasure O)} {H : OutcomeGame J B (ProbabilityMeasure O)}
    [G.Measurable] [H.Measurable]

/-- Law simulation preserves expected Nash with the deviator-reindexed utility
structure. No separate value representation or global integrability is required. -/
theorem transport_expectedNash
    (f : MixtureSimulation IsUnilateralDeviation IsUnilateralDeviation G.toKernel H.toKernel)
    (P : PayoffStructure I O V) {a : ∀ i, A i}
    (ha : (G.expectedNashProblem P).IsEquilibrium a) :
    (H.expectedNashProblem ⟨P.payoff ∘ f.deviatorMap⟩).IsEquilibrium (f.toFun a) :=
  f.transport_ofExpectedValue P.payoff ha

end MathEconLib.GameTheory.MixtureSimulation
