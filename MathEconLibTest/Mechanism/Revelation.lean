/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Mechanism
public import MathEconLib.Probability.FinDist.Measure

/-!
# Multi-agent revelation with a noninvertible message encoding

Two agents buy separate goods at price one. Their types carry a value bit and an irrelevant bit;
messages carry an inverted buying bit and an irrelevant ternary tag. The strategy forgets the
irrelevant type bit and always sends tag zero, so it is neither injective nor surjective.
Values also contain an additive term depending on the other agent's true type.

The canonical direct mechanism is DSIC and truth is a Bayesian equilibrium under a correlated
two-point prior. Both headline revelation principles preserve outcomes and monetary transfers.
A second strategy is suboptimal at null types. Its direct mechanism still has a truthful ex-ante
equilibrium but is not DSIC, separating the two revelation statements.
The public umbrella must expose these results without imposing measurability on dominant-strategy
revelation or decidable equality of players on Bayesian revelation.
-/

@[expose] public noncomputable section

open MathEconLib.GameTheory MathEconLib.Mechanism MathEconLib.Probability MeasureTheory

namespace MathEconLibTest.MechanismRevelation

abbrev Types (_ : Bool) := Bool × Bool
abbrev Actions (_ : Bool) := Bool × Fin 3

def encode (t : Bool × Bool) : Bool × Fin 3 := (!t.1, 0)

def decode (a : Bool × Fin 3) : Bool := !a.1

@[simp] lemma decode_encode (t : Bool × Bool) : decode (encode t) = t.1 := by
  simp [decode, encode]

theorem encode_not_injective : ¬ Function.Injective encode := by
  intro h
  have hp : (false, false) = (false, true) := h rfl
  exact Bool.noConfusion (congrArg Prod.snd hp)

theorem encode_not_surjective : ¬ Function.Surjective encode := by
  intro h
  obtain ⟨t, ht⟩ := h (false, 1)
  have htag := congrArg Prod.snd ht
  norm_num [encode] at htag

def environment : QuasilinearEnvironment Bool Types (Bool → Bool) where
  value i θ o := (if (θ i).1 then 2 else 0) * (if o i then 1 else 0) +
    if (θ (!i)).1 then 3 else 0

theorem not_private_values : ¬ environment.IsPrivateValues := by
  intro h
  have hv := congrFun (h false (fun _ ↦ (false, false)) (fun i ↦ (i, false)) rfl)
    (fun _ ↦ false)
  norm_num [environment] at hv

def indirect : MathEconLib.Mechanism Bool Actions (Bool → Bool) where
  outcome a i := decode (a i)
  transfer i a := if decode (a i) then -1 else 0

def direct : DirectMechanism Bool Types (Bool → Bool) := indirect.comap (fun _ ↦ encode)

lemma utility_le_encoded (θ : Profile Types) (i : Bool) (a : Profile Actions) :
    environment.utility indirect i θ a ≤
      environment.utility indirect i θ (fun j ↦ encode (θ j)) := by
  simp only [QuasilinearEnvironment.utility, environment, indirect, decode_encode]
  split_ifs <;> norm_num

theorem dominant (θ : Profile Types) (i : Bool) :
    StrategicGame.Strategy.IsDominant (G := environment.utilityGame indirect θ) (i := i)
      (encode (θ i)) := by
  intro a'
  refine StrategicGame.Strategy.le_iff'.2 fun a ↦ ?_
  simpa only [QuasilinearEnvironment.utilityGame_payoff, QuasilinearEnvironment.utility,
    environment, indirect, Function.update_self] using
    utility_le_encoded θ i (Function.update a i a')

theorem direct_dsic : DirectMechanism.IsDSIC environment direct :=
  indirect.isDSIC_comap_of_isDominant environment (fun _ ↦ encode) dominant

/-- The existential theorem records the outcomes and transfers, not just truthful incentives. -/
example : ∃ D : DirectMechanism Bool Types (Bool → Bool),
    DirectMechanism.IsDSIC environment D ∧
      (∀ θ, D.outcome θ = indirect.outcome (fun i ↦ encode (θ i))) ∧
      ∀ i θ, D.transfer i θ = indirect.transfer i (fun j ↦ encode (θ j)) :=
  indirect.revelation_principle_dominant environment (fun _ ↦ encode) dominant

def measurableStrategy : (indirect.inducedBayesianGame environment).Strategy :=
  fun _ ↦ ⟨encode, Measurable.of_discrete⟩

theorem source_bne (μ : Measure (Profile Types)) [IsProbabilityMeasure μ] :
    (indirect.inducedBayesianGame environment).IsBNE μ measurableStrategy := by
  refine ⟨fun _ ↦ Integrable.of_finite, ?_⟩
  intro i s' hs'
  change (∫ θ, environment.utility indirect i θ (fun j ↦ (s' j).1 (θ j)) ∂μ) ≤
    ∫ θ, environment.utility indirect i θ (fun j ↦ encode (θ j)) ∂μ
  exact integral_mono hs'.2 Integrable.of_finite (fun θ ↦ utility_le_encoded θ i _)

/-- Both agents have low values together or high values together. -/
def typeLaw : FinDist (Profile Types) :=
  FinDist.mixture ⟨1 / 2, by constructor <;> norm_num⟩
    (FinDist.pure (fun _ ↦ (false, false))) (FinDist.pure (fun _ ↦ (true, true)))

def prior : Measure (Profile Types) := typeLaw.toMeasure

instance : IsProbabilityMeasure prior := inferInstanceAs (IsProbabilityMeasure typeLaw.toMeasure)

theorem truthful_bne : (direct.inducedBayesianGame environment).IsBNE prior
    (DirectMechanism.Quasilinear.truthfulStrategy environment direct) :=
  indirect.isBNE_truthful_comap environment prior measurableStrategy (source_bne prior)

/-- Follow the encoding on supported types and reverse the buying decision at null types. -/
def nullTypeAction (t : Bool × Bool) : Bool × Fin 3 :=
  if t.1 = t.2 then encode t else encode (!t.1, t.2)

def nullTypeStrategy : (indirect.inducedBayesianGame environment).Strategy :=
  fun _ ↦ ⟨nullTypeAction, Measurable.of_discrete⟩

def nullDirect : DirectMechanism Bool Types (Bool → Bool) :=
  indirect.comap (fun i ↦ (nullTypeStrategy i).1)

theorem null_type_source_bne :
    (indirect.inducedBayesianGame environment).IsBNE prior nullTypeStrategy := by
  refine ⟨fun _ ↦ Integrable.of_finite, ?_⟩
  intro i s' hs'
  change (∫ θ, environment.utility indirect i θ (fun j ↦ (s' j).1 (θ j)) ∂prior) ≤
    ∫ θ, environment.utility indirect i θ (fun j ↦ nullTypeAction (θ j)) ∂prior
  calc
    _ ≤ ∫ θ, environment.utility indirect i θ (fun j ↦ encode (θ j)) ∂prior :=
      integral_mono hs'.2 Integrable.of_finite (fun θ ↦ utility_le_encoded θ i _)
    _ = _ := by
      change (∫ θ, environment.utility indirect i θ (fun j ↦ encode (θ j)) ∂typeLaw.toMeasure) =
        ∫ θ, environment.utility indirect i θ (fun j ↦ nullTypeAction (θ j)) ∂typeLaw.toMeasure
      rw [← FinDist.expect_eq_integral, ← FinDist.expect_eq_integral]
      simp [typeLaw, FinDist.expect_mixture, FinDist.expect_pure, nullTypeAction]

theorem null_type_truthful_bne : (nullDirect.inducedBayesianGame environment).IsBNE prior
    (DirectMechanism.Quasilinear.truthfulStrategy environment nullDirect) :=
  indirect.isBNE_truthful_comap environment prior nullTypeStrategy null_type_source_bne

/-- Ex-ante revelation does not assert dominant-strategy incentives at null types. -/
theorem null_direct_not_dsic : ¬ DirectMechanism.IsDSIC environment nullDirect := by
  intro h
  have hh := h false (fun _ ↦ (true, false)) (fun _ ↦ (true, true))
  norm_num [nullDirect, MathEconLib.Mechanism.comap, nullTypeStrategy, nullTypeAction,
    QuasilinearEnvironment.utility, environment, indirect, decode, encode] at hh

example : ∃ D : DirectMechanism Bool Types (Bool → Bool),
    (D.inducedBayesianGame environment).IsBNE prior
      (DirectMechanism.Quasilinear.truthfulStrategy environment D) ∧
      (∀ θ, D.outcome θ = indirect.outcome (fun i ↦ encode (θ i))) ∧
      ∀ i θ, D.transfer i θ = indirect.transfer i (fun j ↦ encode (θ j)) :=
  indirect.revelation_principle_bayesian environment prior measurableStrategy (source_bne prior)

def sampleTypes : Profile Types := fun i ↦ (i, !i)

example : direct.outcome sampleTypes false = false ∧ direct.outcome sampleTypes true = true := by
  constructor <;> rfl

example : direct.payment true sampleTypes = 1 ∧ direct.payment false sampleTypes = 0 := by
  norm_num [MathEconLib.Mechanism.payment, direct, MathEconLib.Mechanism.comap, indirect,
    sampleTypes, decode, encode]

end MathEconLibTest.MechanismRevelation

section Api

universe uI uT uA uO

variable {I : Type uI} {T : I → Type uT} {A : I → Type uA} {O : Type uO}
    (M : MathEconLib.Mechanism I A O) (E : QuasilinearEnvironment I T O)

/-- Dominant-strategy revelation needs neither measurable spaces nor a type prior. -/
example [DecidableEq I] (σ : ∀ i, T i → A i)
    (hσ : ∀ θ i, StrategicGame.Strategy.IsDominant (G := E.utilityGame M θ) (i := i)
      (σ i (θ i))) :
    DirectMechanism.IsDSIC E (M.comap σ) := M.isDSIC_comap_of_isDominant E σ hσ

/-- Bayesian revelation preserves the original convention with no player finiteness or equality. -/
example [∀ i, MeasurableSpace (T i)] [∀ i, MeasurableSpace (A i)]
    (μ : Measure (Profile T)) [IsProbabilityMeasure μ]
    (σ : (M.inducedBayesianGame E).Strategy) (hσ : (M.inducedBayesianGame E).IsBNE μ σ) :
    ((M.comap (fun i ↦ (σ i).1)).inducedBayesianGame E).IsBNE μ
      (DirectMechanism.Quasilinear.truthfulStrategy E (M.comap (fun i ↦ (σ i).1))) :=
  M.isBNE_truthful_comap E μ σ hσ

end Api
