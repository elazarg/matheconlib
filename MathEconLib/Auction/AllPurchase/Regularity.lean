/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.Auction.AllPurchase.Basic
public import MathEconLib.ForMathlib.CDF

/-!
# Continuous all-pay benchmarks

Atomless type laws make the common CDF and its all-pay payment expression
continuous. No density, bounded support or independence is needed.
-/

@[expose] public section

namespace MathEconLib.Auction

open MeasureTheory ProbabilityTheory

variable {Ω : Type} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  {n : ℕ} [NeZero n] (A : Auction Ω n) [A.HasIdenticalTypes] [A.HasAtomlessTypes]

/-- Atomlessness removes every jump of the common CDF. -/
theorem commonCDF_continuous : Continuous A.commonCDF := by
  let : NullSingletonClass (Measure.map (A.θ 0) ℙ) := HasAtomlessTypes.θ_noAtoms
  exact ProbabilityTheory.continuous_cdf _

/-- No density, bounded type support, or independence is needed for this continuity. -/
theorem allPayBid_continuous : Continuous A.allPayBid := by
  have powerCDF : Continuous (fun value => A.commonCDF value ^ (n - 1)) :=
    A.commonCDF_continuous.pow (n - 1)
  exact (continuous_id.mul powerCDF).sub
    (intervalIntegral.continuous_primitive
      (fun first second => powerCDF.intervalIntegrable first second) A.lowestType)

end MathEconLib.Auction
