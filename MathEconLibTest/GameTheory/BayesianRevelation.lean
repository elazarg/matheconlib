/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism.Core.BayesianUtility
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Comap

/-!
# Bayesian revelation through exact strategy translation

Both proofs preserve the same prior, true types, full transfer consequences, incumbent
integrability and integrable-deviation filter. The second pair reuses the literal same
comorphism for an explicit comparison, rather than claiming a second dominant-strategy use.
-/

@[expose] public noncomputable section

namespace MathEconLibTest.GameTheory.BayesianRevelation

open MathEconLib.GameTheory MathEconLib.Mechanism MeasureTheory

universe uI uT uA uO uV

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}
  {V : Type uV} [∀ i, MeasurableSpace (T i)] [∀ i, MeasurableSpace (A i)]
  (M : MathEconLib.Mechanism I A O)
  (u : I → Profile T → (O × (I → ℝ)) → V)
  (μ : Measure (Profile T))
  (s : (M.toBayesianGame u).Strategy)

local notation "G" => MathEconLib.Mechanism.toBayesianGame M u
local notation "D" => MathEconLib.Mechanism.toBayesianGame
  (MathEconLib.Mechanism.comap M (fun i ↦ Subtype.val (s i))) u

/-- Truth is a measurable report strategy, independently of the utility model. -/
def truthful : (D).Strategy := fun _ ↦ ⟨id, measurable_id⟩

/-- Lift reports by executing the indirect strategy at the reported type. -/
def liftReports (reports : (D).Strategy) : (G).Strategy :=
  BayesianGame.Strategy.mapActions (G) s reports

@[simp] theorem liftReports_truthful :
    liftReports M u s (truthful M u s) = s := rfl

/-- Both routes use exactly the same realized payoff with the true type fixed. -/
theorem payoff_liftReports (reports : (D).Strategy) (i : I) (θ : Profile T) :
    (D).payoff i ((D).measurableActionProfile reports θ) θ =
      (G).payoff i ((G).measurableActionProfile (liftReports M u s reports) θ) θ := rfl

/-- A direct deviation changes no opponent after executing the indirect strategies. -/
theorem liftReports_opponents (reports : (D).Strategy) (i : I)
    (agree : ∀ j, j ≠ i → reports j = truthful M u s j) :
    ∀ j, j ≠ i → liftReports M u s reports j = s j := by
  intro j different
  apply Subtype.ext
  funext value
  change (s j).1 ((reports j).1 value) = (s j).1 value
  have same : (reports j).1 value = value :=
    congrArg (fun report : {f : T j → T j // Measurable f} ↦ report.1 value) (agree j different)
  exact congrArg (s j).1 same

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- This wrapper names the same existing certificate for both record clients. -/
def reportComorphism : GameComorphism ((D).bneProblem μ) ((G).bneProblem μ) :=
  (G).comapActionsComorphism μ s

/-- The record route uses the existing action-translation certificate. -/
theorem record_route [LE V] [IsProbabilityMeasure μ] (h : (G).IsBNE μ s) :
    (D).IsBNE μ (truthful M u s) :=
  (reportComorphism M u μ s).pullback h

/-- The direct route lifts measurable deviations and carries their own integrability. -/
theorem direct_route [LE V] [IsProbabilityMeasure μ] (h : (G).IsBNE μ s) :
    (D).IsBNE μ (truthful M u s) := by
  rw [BayesianGame.isBNE_iff] at h ⊢
  refine ⟨?_, h.2⟩
  intro i reports agree integrable
  exact h.1 i (liftReports M u s reports)
    (liftReports_opponents M u s reports i agree) integrable

/-- An explicit comparison can, for example, allow a fixed playerwise error in real values. -/
theorem record_comparison_route (C : I → V → V → Prop)
    (h : ((G).bneProblem μ).IsEquilibriumWith C s) :
    ((D).bneProblem μ).IsEquilibriumWith C (truthful M u s) :=
  (reportComorphism M u μ s).pullbackWith C C (fun _ _ _ _ comparison ↦ comparison) h

/-- The same direct lift also transports the second comparison without a certificate projection. -/
theorem direct_comparison_route (C : I → V → V → Prop)
    (h : ((G).bneProblem μ).IsEquilibriumWith C s) :
    ((D).bneProblem μ).IsEquilibriumWith C (truthful M u s) := by
  rw [EquilibriumProblem.isEquilibriumWith_iff] at h ⊢
  refine ⟨h.1, ?_⟩
  intro i reports deviation
  exact h.2 i (liftReports M u s reports)
    ⟨liftReports_opponents M u s reports i deviation.1, deviation.2⟩

/-- A factored direct proof reuses its comparison theorem for ordinary BNE. -/
theorem direct_reused_route [LE V] [IsProbabilityMeasure μ] (h : (G).IsBNE μ s) :
    (D).IsBNE μ (truthful M u s) :=
  (EquilibriumProblem.isEquilibriumWith_le_iff _ _).mp
    (direct_comparison_route M u μ s _
      ((EquilibriumProblem.isEquilibriumWith_le_iff _ _).mpr h))

end MathEconLibTest.GameTheory.BayesianRevelation
