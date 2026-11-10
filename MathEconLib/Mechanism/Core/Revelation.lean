/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism.Core.BayesianIC
public import MathEconLib.GameTheory.Strategic.Bayesian.Measurable.Comap

/-!
# Multi-agent revelation through action translation

Given a pure strategy profile `σ`, the direct mechanism `M.comap σ` executes the original
strategy on each reported type. It preserves outcomes and transfers at every report profile.
Dominant strategies in the original mechanism make the direct mechanism DSIC. A measurable
Bayesian equilibrium makes truthful reporting an equilibrium under the same prior.

The natural map goes from reports to original actions, not conversely. A report deviation
therefore induces an original action deviation. Bayesian equilibrium pulls back through the
existing `BayesianGame.IsBNE.comapActions`, whose proof uses a `GameComorphism`.
Neither injectivity nor surjectivity of the strategy maps is required.

The environment is quasilinear and may have interdependent values. The Bayesian conclusion is
ex-ante `IsBNE`, with its integrable-deviation convention. Pointwise conditional BIC, including
incentives at null types, requires additional hypotheses. Both results concern pure strategies.

## Main statements

* `Mechanism.isDSIC_comap_of_isDominant`: The canonical direct mechanism is DSIC.
* `Mechanism.revelation_principle_dominant`: A DSIC direct mechanism preserves equilibrium outcomes
  and transfers.
* `Mechanism.isBNE_truthful_comap`: Truth is a Bayesian equilibrium of the canonical direct
  mechanism.
* `Mechanism.revelation_principle_bayesian`: A truthful ex-ante direct mechanism preserves
  equilibrium outcomes and transfers.

## References

Jason D. Hartline (2016), *Mechanism Design and Approximation*, Section 2.10, Theorem 2.10.1.
[Manuscript](https://jasonhartline.com/MDnA/MDnA-ch2.pdf).
The statements here use the library's quasilinear environments and ex-ante Bayesian convention.

## Tags

mechanism design, revelation principle, dominant strategies, bayesian equilibrium, comorphism
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MeasureTheory

namespace MathEconLib.Mechanism

universe uI uT uA uO

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}
    (M : Mechanism I A O) (E : QuasilinearEnvironment I T O)

/-- Executing a dominant strategy on each reported type makes truthful reporting dominant. -/
theorem isDSIC_comap_of_isDominant [DecidableEq I] (σ : ∀ i, T i → A i)
    (hσ : ∀ θ i, StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (i := i)
      (σ i (θ i))) :
    DirectMechanism.IsDSIC E (M.comap σ) := by
  intro i θ r
  have h := StrategicGame.Strategy.le_iff'.1 (hσ θ i (σ i (r i))) (fun j ↦ σ j (r j))
  change E.utility M i θ (fun j ↦ σ j (r j)) ≤
    E.utility M i θ (fun j ↦ σ j (Function.update r i (θ i) j))
  rw [funext (Function.apply_update σ r i (θ i))]
  simpa only [QuasilinearEnvironment.utilityGame_payoff, Function.update_eq_self] using h

/-- A mechanism with a dominant pure strategy for each type has a DSIC direct realization with
the same outcome and transfers at every true type profile. -/
theorem revelation_principle_dominant [DecidableEq I] (σ : ∀ i, T i → A i)
    (hσ : ∀ θ i, StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (i := i)
      (σ i (θ i))) :
    ∃ D : DirectMechanism I T O, DirectMechanism.IsDSIC E D ∧
      (∀ θ, D.outcome θ = M.outcome (fun i ↦ σ i (θ i))) ∧
      ∀ i θ, D.transfer i θ = M.transfer i (fun j ↦ σ j (θ j)) :=
  ⟨M.comap σ, M.isDSIC_comap_of_isDominant E σ hσ, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

section Bayesian

variable [∀ i, MeasurableSpace (T i)] [∀ i, MeasurableSpace (A i)]
    (μ : Measure (Profile T)) [IsProbabilityMeasure μ]

/-- Executing a measurable Bayesian equilibrium on reported types makes truth a Bayesian
equilibrium. Integrability and the prior are preserved by the action comorphism. -/
theorem isBNE_truthful_comap (σ : (M.inducedBayesianGame E).Strategy)
    (hσ : (M.inducedBayesianGame E).IsBNE μ σ) :
    ((M.comap (fun i ↦ (σ i).1)).inducedBayesianGame E).IsBNE μ
      (DirectMechanism.Quasilinear.truthfulStrategy E (M.comap (fun i ↦ (σ i).1))) := by
  apply BayesianGame.IsBNE.comapActions (G := M.inducedBayesianGame E) σ
  exact hσ

/-- A measurable pure Bayesian equilibrium has a direct realization in which truth is an
ex-ante equilibrium, with the same outcome and transfers at every true type profile. -/
theorem revelation_principle_bayesian (σ : (M.inducedBayesianGame E).Strategy)
    (hσ : (M.inducedBayesianGame E).IsBNE μ σ) :
    ∃ D : DirectMechanism I T O,
      (D.inducedBayesianGame E).IsBNE μ (DirectMechanism.Quasilinear.truthfulStrategy E D) ∧
      (∀ θ, D.outcome θ = M.outcome (fun i ↦ (σ i).1 (θ i))) ∧
      ∀ i θ, D.transfer i θ = M.transfer i (fun j ↦ (σ j).1 (θ j)) :=
  ⟨M.comap (fun i ↦ (σ i).1), M.isBNE_truthful_comap E μ σ hσ, fun _ ↦ rfl, fun _ _ ↦ rfl⟩

end Bayesian

end MathEconLib.Mechanism
