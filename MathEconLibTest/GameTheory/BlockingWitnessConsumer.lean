/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibTest.GameTheory.BlockingWitness
public import MathEconLib.Matching.Classical.Marriage.ToContracts

/-!
# From blocking contract sets to native matching witnesses

Two independently meaningful reductions compose: shrink a blocking contract set
to one of its members, then interpret a singleton block as a marriage blocking
pair. The composite retains membership in the original proposal. Individual
rationality is explicit in the matching-state type.
-/

@[expose] public section

namespace MathEconLibTest.AbstractionExperiments.BlockingWitnessConsumer

open Set MathEconLib.Matching

/-- Substitutes refine contract-set witnesses into singleton witnesses from that set. -/
def singletonLift {B S X : Type*} (M : Market B S X) (hsub : M.Substitutable) :
    WitnessLift (fun A z => M.Blocks A {z}) M.Blocks where
  state := id
  related _ Z z := z ∈ Z
  covers _ _ blocks := Market.Blocks.exists_singleton M hsub blocks

/-- The singleton marriage dictionary preserves the identity of the proposed pair. -/
def marriageLift {M W : Type*} (mkt : MarriageMarket M W) :
    WitnessLift
      (fun (c : {μ : M ≃. W // mkt.IndividuallyRational μ}) (p : M × W) =>
        mkt.IsBlockingPair c.1 p.1 p.2)
      (fun A (p : M × W) => mkt.toContractsMarket.Blocks A {p}) where
  state c := mkt.graphOf c.1
  related _ p original := p = original
  covers c p blocks := ⟨p, rfl, (mkt.blocks_singleton_graphOf_iff c.2).mp blocks⟩

/-- The composed certificate extracts a genuine pair belonging to the initial proposal. -/
theorem blockingPair_from_composite {M W : Type*} (mkt : MarriageMarket M W)
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) {Z : Set (M × W)}
    (blocks : mkt.toContractsMarket.Blocks (mkt.graphOf μ) Z) :
    ∃ p ∈ Z, mkt.IsBlockingPair μ p.1 p.2 := by
  let composite := (singletonLift mkt.toContractsMarket mkt.substitutable_toContractsMarket).comp
    (marriageLift mkt)
  obtain ⟨p, ⟨original, member, equal⟩, pairBlocks⟩ := composite.covers ⟨μ, hIR⟩ Z blocks
  exact ⟨p, equal ▸ member, pairBlocks⟩

/-- The same witness certificate transports pairwise stability, retaining incumbent IR. -/
theorem stability_from_singletonLift {B S X : Type*} (M : Market B S X)
    (hsub : M.Substitutable) {A : Set X} (stable : M.PairwiseStable A) : M.Stable A :=
  ⟨stable.1, (singletonLift M hsub).transport stable.2⟩

end MathEconLibTest.AbstractionExperiments.BlockingWitnessConsumer
