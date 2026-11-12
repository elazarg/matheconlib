/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.ForMathlib.WitnessLift
public import MathEconLib.Matching.Contracts.Basic

/-!
# Singleton blocking certificates for contract markets

Substitutability turns a blocking contract set into a singleton block from that
set. The optional certificate retains membership in the original proposal and
can compose with other witness translations. No finiteness or consistency
assumption is imposed.
-/

@[expose] public section

namespace MathEconLib.Matching.Market

universe u v w

/-- A joint block lifts to a singleton block belonging to the original proposal. -/
def singletonBlockingLift {B : Type u} {S : Type v} {X : Type w}
    (M : Market B S X) (substitutable : M.Substitutable) :
    WitnessLift (fun A z => M.Blocks A {z}) M.Blocks where
  state := id
  related _ proposal contract := contract ∈ proposal
  covers _ _ blocks := Blocks.exists_singleton M substitutable blocks

end MathEconLib.Matching.Market
