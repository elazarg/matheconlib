/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.UniformTwoBidder
public import MathEconLib.Auction.AllPurchase.WithPrice

/-!
# The zero-baseline endpoint equilibrium

At posted price `5/2`, the same independent uniform bidders use `v/2`.
Their quadratic marginal cost at zero is zero and their lowest-type utility
vanishes. The generic continuous-strategy coverage theorem rejects every real
bid, including negative bids, and native averaging gives Bayesian equilibrium.
This is a boundary certificate: its zero marginal cost excludes an interior
strategy certificate.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase.UniformBoundaryEquilibrium

open MeasureTheory ProbabilityTheory Set
open UniformProbability

abbrev model : LinearScarcityAuction Ω 2 :=
  UniformTwoBidder.model.withPrice (5 / 2) (by norm_num)

def strategy (value : ℝ) : ℝ := value / 2

theorem strategy_measurable : Measurable strategy := measurable_id.div_const 2

theorem strategy_strictMono : StrictMono strategy := by
  intro first second less
  dsimp only [strategy]
  linarith

theorem strategy_strictMonoOn :
    StrictMonoOn strategy (Icc model.lowestType model.highestType) := by
  intro first _ second _ less
  exact strategy_strictMono less

theorem strategy_continuousOn :
    ContinuousOn strategy (Icc model.lowestType model.highestType) :=
  (continuous_id.div_const 2).continuousOn

theorem strategy_integrable (i : Fin 2) :
    Integrable (fun sample => strategy (model.θ i sample)) ℙ :=
  (integrable_value i).div_const 2

theorem mean_strategy (i : Fin 2) :
    (∫ sample, strategy (model.θ i sample) ∂ℙ) = 1 / 2 := by
  change (∫ sample, value i sample / 2 ∂ℙ) = 1 / 2
  rw [integral_div, integral_value]

theorem meanPurchase_eq : model.meanPurchase strategy = 1 / 2 := mean_strategy 0

theorem K_eq : model.K_linear strategy = 0 := by
  rw [LinearScarcityAuction.K_linear, meanPurchase_eq]
  change (5 / 2 : ℝ) - 3 + 1 * (2 - 1) * (1 / 2) = 0
  norm_num

theorem winning_probability (i : Fin 2) (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    model.q_strat strategy i (strategy v) = v / 2 := by
  rw [model.toAuction.q_strat_at_strictMono_eq model.spec.usesStrictHighestBidAllocation
    strategy_strictMonoOn strategy_measurable i member]
  have cdf : model.commonCDF v = v / 2 := UniformTwoBidder.commonCDF_eq v member
  norm_num [cdf]

theorem interim_payment (i : Fin 2) (bid : ℝ) : model.p_strat strategy i bid = bid ^ 2 := by
  rw [model.p_strat_eq_quadratic strategy strategy_measurable strategy_integrable i bid, K_eq]
  change 1 * bid ^ 2 + 0 * bid = bid ^ 2
  ring

abbrev problem (i : Fin 2) : BidderProblem :=
  model.toBidderProblem model.spec.isUnitIntervalAllocation strategy i

private theorem payoff_on_strategy (i : Fin 2) (v w : ℝ)
    (reportMember : w ∈ Icc (0 : ℝ) 2) :
    (problem i).payoff v (strategy w) = v * w / 2 - w ^ 2 / 4 := by
  change v * model.q_strat strategy i (strategy w) - model.p_strat strategy i (strategy w) = _
  rw [winning_probability i w reportMember, interim_payment]
  dsimp only [strategy]
  ring

instance typeDeviationIC (i : Fin 2) : (problem i).HasTypeDeviationIC where
  typeDeviationIC v valid w validReport := by
    change (problem i).payoff v (strategy w) ≤ (problem i).payoff v (strategy v)
    rw [payoff_on_strategy i v w validReport, payoff_on_strategy i v v valid]
    nlinarith [sq_nonneg (v - w)]

theorem utility_eq (i : Fin 2) (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    (problem i).U v = v ^ 2 / 4 := by
  change (problem i).payoff v (strategy v) = _
  rw [payoff_on_strategy i v v member]
  ring

instance boundaryRegime (i : Fin 2) : BidderProblem.IsBoundaryRegime (problem i) where
  U_lowestType_zero := by
    change (problem i).U 0 = 0
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div] using utility_eq i 0 (by norm_num)

/-- Native action coverage supplies original-bid incentives without an interior assumption. -/
theorem hasUniversalIC (i : Fin 2) : (problem i).HasUniversalIC Set.univ := by
  apply model.hasUniversalIC_of_continuous_strategy strategy strategy_measurable
    strategy_strictMonoOn strategy_continuousOn ?_ i (typeDeviationIC i)
  rw [K_eq]
  change (0 : ℝ) / 2 = -0 / (2 * 1)
  norm_num

theorem strategy_isBNE :
    model.toAuction.bayesianGame.IsBNE model.typeLaw
      (model.toAuction.bidStrategy strategy strategy_measurable) :=
  model.isBNE_of_universalIC strategy strategy_measurable
    strategy_strictMonoOn.monotoneOn hasUniversalIC

/-- Zero marginal cost is incompatible with the native negative-cost interior condition. -/
theorem not_interior (i : Fin 2) : ¬ model.IsInteriorRegimeStrategy strategy i := by
  intro interior
  have negative := interior.K_neg
  rw [K_eq] at negative
  exact (lt_irrefl (0 : ℝ)) negative

end MathEconLib.Examples.AllPurchase.UniformBoundaryEquilibrium
