/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Matching.Contracts.BlockingWitnesses
public import MathEconLib.Matching.Classical.Marriage.ToContracts

/-!
# Blocking-witness certificates for marriage and contracts

Individual rationality belongs to the matching state supplied to the
singleton dictionary. Composing it with contract-set decomposition retains a
singleton contract block, original-proposal membership and the identity of the
native blocking pair. The construction allows infinite markets and proposals.
-/

@[expose] public section

namespace MathEconLib.Matching.MarriageMarket

universe u v

variable {M : Type u} {W : Type v}

/-- A singleton contract block of an individually rational matching is a native blocking pair. -/
def singletonBlockingPairLift (market : MarriageMarket M W) :
    WitnessLift
      (fun (state : {matching : M ≃. W // market.IndividuallyRational matching}) (pair : M × W) =>
        market.IsBlockingPair state.1 pair.1 pair.2)
      (fun contracts (pair : M × W) => market.toContractsMarket.Blocks contracts {pair}) where
  state certified := market.graphOf certified.1
  related _ pair original := pair = original
  covers certified pair blocks :=
    ⟨pair, rfl, (market.blocks_singleton_graphOf_iff certified.2).mp blocks⟩

/-- A contract-set block lifts to a native pair with its actual singleton-block provenance. -/
def blockingPairLift (market : MarriageMarket M W) :
    WitnessLift
      (fun (state : {matching : M ≃. W // market.IndividuallyRational matching}) (pair : M × W) =>
        market.IsBlockingPair state.1 pair.1 pair.2)
      (fun contracts (proposal : Set (M × W)) =>
        market.toContractsMarket.Blocks contracts proposal) :=
  (market.toContractsMarket.singletonBlockingLift market.substitutable_toContractsMarket).comp
    market.singletonBlockingPairLift

end MathEconLib.Matching.MarriageMarket
