/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Matching.Classical.Marriage.BlockingWitnesses

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

/-- Composition retains the actual intermediate singleton block as well as the native pair. -/
theorem blockingPair_from_composite {M W : Type*} (mkt : MarriageMarket M W)
    {μ : M ≃. W} (hIR : mkt.IndividuallyRational μ) {Z : Set (M × W)}
    (blocks : mkt.toContractsMarket.Blocks (mkt.graphOf μ) Z) :
    ∃ p ∈ Z, mkt.toContractsMarket.Blocks (mkt.graphOf μ) {p} ∧
      mkt.IsBlockingPair μ p.1 p.2 := by
  obtain ⟨p, ⟨original, singletonBlock, member, equal⟩, pairBlocks⟩ :=
    mkt.blockingPairLift.covers ⟨μ, hIR⟩ Z blocks
  exact ⟨p, equal ▸ member, equal ▸ singletonBlock, pairBlocks⟩

/-- The same witness certificate transports pairwise stability, retaining incumbent IR. -/
theorem stability_from_singletonLift {B S X : Type*} (M : Market B S X)
    (hsub : M.Substitutable) {A : Set X} (stable : M.PairwiseStable A) : M.Stable A :=
  ⟨stable.1, (M.singletonBlockingLift hsub).transport stable.2⟩

end MathEconLibTest.AbstractionExperiments.BlockingWitnessConsumer
