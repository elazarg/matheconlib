/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.UniformTwoBidder
public import MathEconLib.Auction.AllPurchase.WithPrice
public import MathEconLib.Auction.AllPurchase.RestrictedBayesianEquilibrium

/-!
# A positive-marginal-cost uniform boundary model

The strategy `(sqrt (1 + v²) - 1) / 2` is globally nonnegative. Its actual
uniform mean determines the positive posted price `4 - mean`, making marginal
quadratic cost equal to one. Report incentives and zero lowest-type utility
hold in the actual repriced auction. Negative bids remain available in its
signed action space and defeat pointwise all-real IC; the calculation alone
is not a claim about failure of ex-ante Bayesian equilibrium at a null type.
The typed nonnegative strategy is native Bayesian Nash under the actual prior,
against all admitted measurable type-dependent nonnegative deviations.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase.PositiveKBoundary

open MeasureTheory ProbabilityTheory Set
open UniformProbability
open scoped NNReal

def strategy (value : ℝ) : ℝ := (Real.sqrt (1 + value ^ 2) - 1) / 2

theorem strategy_continuous : Continuous strategy :=
  ((Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))).sub
    continuous_const).div_const 2

theorem strategy_measurable : Measurable strategy := strategy_continuous.measurable

theorem strategy_nonneg (v : ℝ) : 0 ≤ strategy v := by
  have bound : 1 ≤ Real.sqrt (1 + v ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg v])
  dsimp only [strategy]
  linarith

theorem strategy_le_half {v : ℝ} (nonnegative : 0 ≤ v) : strategy v ≤ v / 2 := by
  have bound : Real.sqrt (1 + v ^ 2) ≤ v + 1 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  dsimp only [strategy]
  linarith

theorem strategy_bounds (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    0 ≤ strategy v ∧ strategy v ≤ v / 2 :=
  ⟨strategy_nonneg v, strategy_le_half member.1⟩

theorem strategy_zero : strategy 0 = 0 := by norm_num [strategy]

/-- The quadratic net cost at a report is its all-pay benchmark. -/
theorem strategy_quadratic (v : ℝ) : strategy v ^ 2 + strategy v = v ^ 2 / 4 := by
  have square := Real.sq_sqrt (show 0 ≤ 1 + v ^ 2 by nlinarith [sq_nonneg v])
  dsimp only [strategy]
  nlinarith

private theorem integrable_strategy_value (i : Fin 2) :
    Integrable (fun sample => strategy (value i sample)) ℙ := by
  refine (integrable_const (1 : ℝ)).mono'
    (strategy_measurable.comp (measurable_value i)).aestronglyMeasurable ?_
  apply ae_of_all
  intro sample
  rw [Real.norm_eq_abs, abs_of_nonneg (strategy_nonneg _)]
  have bounds := strategy_bounds (value i sample) (value_mem i sample)
  linarith [(value_mem i sample).2]

/-- The mean is taken under the original uniform probability model. -/
def meanBid : ℝ := ∫ sample, strategy (value 0 sample) ∂ℙ

theorem meanBid_nonneg : 0 ≤ meanBid := integral_nonneg (fun _ => strategy_nonneg _)

theorem meanBid_le_half : meanBid ≤ 1 / 2 := by
  have bound := integral_mono (integrable_strategy_value 0) ((integrable_value 0).div_const 2)
    (fun sample => strategy_le_half (value_mem 0 sample).1)
  rw [integral_div, integral_value] at bound
  exact bound

def price : ℝ := 4 - meanBid

theorem price_pos : 0 < price := by
  dsimp only [price]
  linarith [meanBid_le_half]

abbrev model : LinearScarcityAuction Ω 2 :=
  UniformTwoBidder.model.withPrice price price_pos

theorem typeLaw_eq : model.typeLaw = UniformTwoBidder.model.typeLaw := rfl

theorem strategy_continuousOn :
    ContinuousOn strategy (Icc model.lowestType model.highestType) :=
  strategy_continuous.continuousOn

theorem strategy_strictMonoOn :
    StrictMonoOn strategy (Icc model.lowestType model.highestType) := by
  intro first firstMember second _ less
  have nonnegative : 0 ≤ first := firstMember.1
  have squares : first ^ 2 < second ^ 2 := by
    have positive : 0 < (second - first) * (second + first) :=
      mul_pos (sub_pos.mpr less) (by linarith)
    nlinarith
  have rootLess := Real.sqrt_lt_sqrt
    (show 0 ≤ 1 + first ^ 2 by nlinarith [sq_nonneg first])
    (show 1 + first ^ 2 < 1 + second ^ 2 by linarith)
  dsimp only [strategy]
  linarith

theorem strategy_integrable (i : Fin 2) :
    Integrable (fun sample => strategy (model.θ i sample)) ℙ := integrable_strategy_value i

theorem mean_strategy (i : Fin 2) :
    (∫ sample, strategy (model.θ i sample) ∂ℙ) = meanBid :=
  UniformTwoBidder.model.toAuction.integral_comp_type_eq strategy strategy_measurable i 0

theorem meanPurchase_eq : model.meanPurchase strategy = meanBid := rfl

theorem K_eq : model.K_linear strategy = 1 := by
  rw [LinearScarcityAuction.K_linear, meanPurchase_eq]
  change price - 3 + 1 * (2 - 1) * meanBid = 1
  dsimp only [price]
  ring

theorem winning_probability (i : Fin 2) (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    model.q_strat strategy i (strategy v) = v / 2 := by
  rw [model.toAuction.q_strat_at_strictMono_eq model.spec.usesStrictHighestBidAllocation
    strategy_strictMonoOn strategy_measurable i member]
  have cdf : model.commonCDF v = v / 2 := UniformTwoBidder.commonCDF_eq v member
  norm_num [cdf]

theorem interim_payment (i : Fin 2) (bid : ℝ) :
    model.p_strat strategy i bid = bid ^ 2 + bid := by
  rw [model.p_strat_eq_quadratic strategy strategy_measurable strategy_integrable i bid, K_eq]
  change 1 * bid ^ 2 + 1 * bid = bid ^ 2 + bid
  ring

abbrev problem (i : Fin 2) : BidderProblem :=
  model.toBidderProblem model.spec.isUnitIntervalAllocation strategy i

theorem payoff_on_strategy (i : Fin 2) (v w : ℝ) (member : w ∈ Icc (0 : ℝ) 2) :
    (problem i).payoff v (strategy w) = v * w / 2 - w ^ 2 / 4 := by
  change v * model.q_strat strategy i (strategy w) - model.p_strat strategy i (strategy w) = _
  rw [winning_probability i w member, interim_payment]
  linarith [strategy_quadratic w]

instance typeDeviationIC (i : Fin 2) : (problem i).HasTypeDeviationIC where
  typeDeviationIC v member w reportMember := by
    change (problem i).payoff v (strategy w) ≤ (problem i).payoff v (strategy v)
    rw [payoff_on_strategy i v w reportMember, payoff_on_strategy i v v member]
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

/-- The report comparison extends to every original nonnegative bid. -/
theorem hasUniversalIC_nonnegative (i : Fin 2) :
    (problem i).HasUniversalIC (Ici 0) := by
  apply model.hasUniversalIC_nonnegative_of_continuous_strategy strategy strategy_measurable
    strategy_strictMonoOn strategy_continuousOn strategy_zero ?_ i (typeDeviationIC i)
  rw [K_eq]
  norm_num

/-- This is a globally nonnegative action-valued strategy, including off-support types. -/
def nnrealStrategy (v : ℝ) : ℝ≥0 := ⟨strategy v, strategy_nonneg v⟩

theorem nnrealStrategy_measurable : Measurable nnrealStrategy :=
  Measurable.subtype_mk strategy_measurable

@[simp] theorem coe_nnrealStrategy (v : ℝ) : (nnrealStrategy v : ℝ) = strategy v := rfl

/-- The signed bid is allowed by the real-action model and always loses the prize. -/
theorem negative_payoff (i : Fin 2) (v : ℝ) :
    (problem i).payoff v (-(1 / 2)) = 1 / 4 := by
  have allocation : model.q_strat strategy i (-(1 / 2)) = 0 :=
    model.toAuction.q_strat_eq_zero_of_le_lowest model.spec.usesStrictHighestBidAllocation
      strategy_strictMonoOn.monotoneOn i (by
        change (-(1 / 2) : ℝ) ≤ strategy 0
        rw [strategy_zero]
        norm_num)
  change v * model.q_strat strategy i (-(1 / 2)) - model.p_strat strategy i (-(1 / 2)) = _
  rw [allocation, interim_payment]
  norm_num

/-- This is a pointwise all-real-IC obstruction, not an ex-ante non-equilibrium claim. -/
theorem not_all_real_IC (i : Fin 2) : ¬ (problem i).HasUniversalIC Set.univ := by
  intro universal
  have comparison := universal.universalIC 0 (by change (0 : ℝ) ∈ Icc 0 2; norm_num)
    (-(1 / 2)) (Set.mem_univ _)
  change (problem i).payoff 0 (-(1 / 2)) ≤ (problem i).U 0 at comparison
  rw [negative_payoff, utility_eq i 0 (by norm_num)] at comparison
  norm_num at comparison

/-- Native Bayesian equilibrium in the actual nonnegative-action game. -/
theorem strategy_isBNE :
    (model.toAuction.bayesianGame.comapActions (fun _ => (Subtype.val : ℝ≥0 → ℝ))).IsBNE
      model.typeLaw (model.toAuction.restrictedBidStrategy (Ici 0)
        nnrealStrategy nnrealStrategy_measurable) :=
  model.isBNE_nonnegative_of_universalIC nnrealStrategy nnrealStrategy_measurable
    strategy_strictMonoOn.monotoneOn hasUniversalIC_nonnegative

end MathEconLib.Examples.AllPurchase.PositiveKBoundary
