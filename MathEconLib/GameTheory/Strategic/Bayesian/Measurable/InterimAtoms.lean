/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.InterimConverse

/-!
# Interim optimality at types with nonzero marginal mass

An almost-everywhere interim comparison applies at every type whose singleton
has nonzero marginal measure. Null types require additional conditional-belief
data and cannot be recovered from an ex-ante equilibrium verdict.
-/

@[expose] public noncomputable section

namespace MathEconLib.GameTheory.BayesianGame

open MeasureTheory BayesianPrior

variable {I : Type*} {Θ A : I → Type*} [DecidableEq I]
  [∀ i, MeasurableSpace (Θ i)] [∀ i, MeasurableSpace (A i)]
  {G : BayesianGame I Θ A ℝ} {μ : Measure (∀ i, Θ i)}
  {B : ConditionalBeliefs μ} {s : G.Strategy}

/-- Nonzero marginal mass makes a type available to every conull incentive comparison. -/
theorem IsAEInterimBestResponse.at_nonzero_atom
    (optimal : G.IsAEInterimBestResponse μ B s) (i : I) (type : Θ i)
    (mass : marginalType μ i {type} ≠ 0) :
    ∀ action : A i,
      G.interimPayoffAction μ B i type action s ≤ G.interimPayoff μ B i type s := by
  have visits : ∃ᵐ candidate ∂(marginalType μ i), candidate ∈ ({type} : Set (Θ i)) :=
    frequently_ae_mem_iff.mpr mass
  obtain ⟨candidate, member, comparison⟩ := (visits.and_eventually (optimal i)).exists
  have equal : candidate = type := Set.mem_singleton_iff.mp member
  subst candidate
  exact comparison

variable [∀ i, StandardBorelSpace (Θ i)] [∀ i, Nonempty (Θ i)]
  [∀ i, StandardBorelSpace (A i)] [IsProbabilityMeasure μ]

/-- Ex-ante equilibrium implies pointwise interim optimality at nonzero marginal atoms,
under the same measurability and simultaneous integrability guards as the a.e. converse. -/
theorem IsBNE.interim_bestResponse_of_nonzero_atom (equilibrium : G.IsBNE μ s)
    (measurable_payoff : ∀ i,
      Measurable (fun point : (∀ j, A j) × (∀ j, Θ j) =>
        G.payoff i point.1 point.2))
    (integrable_deviations : G.HasIntegrableInterimDeviations μ B s)
    (i : I) (type : Θ i) (mass : marginalType μ i {type} ≠ 0) :
    ∀ action : A i,
      G.interimPayoffAction μ B i type action s ≤ G.interimPayoff μ B i type s :=
  IsAEInterimBestResponse.at_nonzero_atom
    (G.ae_interim_of_isBNE μ B measurable_payoff s equilibrium integrable_deviations)
    i type mass

end MathEconLib.GameTheory.BayesianGame
