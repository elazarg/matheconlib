/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLibExamples.AllPurchase.UniformTwoBidder
public import MathEconLib.Auction.AllPurchase.WithPrice

/-!
# Interior equilibria along an actual posted-price family

Two bidders retain their independent uniform values on `[0, 2]` and the
strict-highest-bid allocation. Changing the positive posted price changes the
actual transfers while preserving scarcity and the type law. For prices below
`5/2`, the affine purchase strategy has positive baseline, negative marginal
cost at zero, and the interior lowest-type utility. Native original-bid and
Bayesian incentive theorems certify the same strategy against all admitted
measurable unilateral strategy deviations.
-/

@[expose] public noncomputable section

namespace MathEconLib.Examples.AllPurchase.UniformPriceFamily

open MeasureTheory ProbabilityTheory Set
open UniformProbability

/-- Positive posted prices for which the affine equilibrium is in the interior regime. -/
abbrev Price := {price : ℝ // price ∈ Ioo 0 (5 / 2)}

abbrev model (price : Price) : LinearScarcityAuction Ω 2 :=
  UniformTwoBidder.model.withPrice price.val price.property.1

/-- The family uses the original joint value law at every price. -/
theorem typeLaw_eq (price : Price) :
    (model price).typeLaw = UniformTwoBidder.model.typeLaw := rfl

/-- Purchases of the lowest type at the selected price. -/
def baseline (price : Price) : ℝ := (5 - 2 * price.val) / 6

theorem baseline_pos (price : Price) : 0 < baseline price := by
  dsimp only [baseline]
  linarith [price.property.2]

def strategy (price : Price) (value : ℝ) : ℝ := baseline price + value / 2

theorem strategy_measurable (price : Price) : Measurable (strategy price) :=
  measurable_const.add (measurable_id.div_const 2)

theorem strategy_strictMono (price : Price) : StrictMono (strategy price) := by
  intro first second less
  dsimp only [strategy]
  linarith

theorem strategy_strictMonoOn (price : Price) :
    StrictMonoOn (strategy price) (Icc (model price).lowestType (model price).highestType) := by
  intro first _ second _ less
  exact strategy_strictMono price less

theorem strategy_integrable (price : Price) (i : Fin 2) :
    Integrable (fun sample => strategy price ((model price).θ i sample)) ℙ := by
  change Integrable (fun sample => baseline price + value i sample / 2) ℙ
  exact (integrable_const _).add ((integrable_value i).div_const 2)

theorem mean_strategy (price : Price) (i : Fin 2) :
    (∫ sample, strategy price ((model price).θ i sample) ∂ℙ) = (4 - price.val) / 3 := by
  change (∫ sample, baseline price + value i sample / 2 ∂ℙ) = (4 - price.val) / 3
  rw [integral_add (integrable_const _) ((integrable_value i).div_const 2),
    integral_div 2 (value i), integral_value, integral_const, probReal_univ, one_smul]
  dsimp only [baseline]
  ring

theorem meanPurchase_eq (price : Price) :
    (model price).meanPurchase (strategy price) = (4 - price.val) / 3 :=
  mean_strategy price 0

theorem K_eq (price : Price) :
    (model price).K_linear (strategy price) = (2 * price.val - 5) / 3 := by
  rw [LinearScarcityAuction.K_linear, meanPurchase_eq]
  change price.val - 3 + 1 * ((2 : ℝ) - 1) * ((4 - price.val) / 3) =
    (2 * price.val - 5) / 3
  ring

theorem K_eq_neg_two_baseline (price : Price) :
    (model price).K_linear (strategy price) = -2 * baseline price := by
  rw [K_eq]
  dsimp only [baseline]
  ring

theorem K_neg (price : Price) : (model price).K_linear (strategy price) < 0 := by
  rw [K_eq_neg_two_baseline]
  linarith [baseline_pos price]

theorem commonCDF_eq (price : Price) (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    (model price).commonCDF v = v / 2 := by
  change cdf (Measure.map (value 0) ℙ) v = v / 2
  exact cdf_value 0 v member

/-- Altering price preserves the on-strategy probability of winning the prize. -/
theorem winning_probability (price : Price) (i : Fin 2) (v : ℝ)
    (member : v ∈ Icc (0 : ℝ) 2) :
    (model price).q_strat (strategy price) i (strategy price v) = v / 2 := by
  rw [(model price).toAuction.q_strat_at_strictMono_eq
    (model price).spec.usesStrictHighestBidAllocation (strategy_strictMonoOn price)
    (strategy_measurable price) i member]
  norm_num [commonCDF_eq price v member]

/-- Net payment includes the resale proceeds under the price-indexed mechanism. -/
theorem interim_payment (price : Price) (i : Fin 2) (bid : ℝ) :
    (model price).p_strat (strategy price) i bid = bid ^ 2 - 2 * baseline price * bid := by
  rw [(model price).p_strat_eq_quadratic (strategy price) (strategy_measurable price)
    (strategy_integrable price) i bid, K_eq_neg_two_baseline]
  change 1 * bid ^ 2 + (-2 * baseline price) * bid = _
  ring

abbrev problem (price : Price) (i : Fin 2) : BidderProblem :=
  (model price).toBidderProblem (model price).spec.isUnitIntervalAllocation (strategy price) i

theorem payoff_on_strategy (price : Price) (i : Fin 2) (v w : ℝ)
    (reportMember : w ∈ Icc (0 : ℝ) 2) :
    (problem price i).payoff v (strategy price w) =
      v * w / 2 - w ^ 2 / 4 + baseline price ^ 2 := by
  change v * (model price).q_strat (strategy price) i (strategy price w) -
    (model price).p_strat (strategy price) i (strategy price w) = _
  rw [winning_probability price i w reportMember, interim_payment]
  dsimp only [strategy]
  ring

theorem utility_eq (price : Price) (i : Fin 2) (v : ℝ) (member : v ∈ Icc (0 : ℝ) 2) :
    (problem price i).U v = v ^ 2 / 4 + baseline price ^ 2 := by
  change (problem price i).payoff v (strategy price v) = _
  rw [payoff_on_strategy price i v v member]
  ring

instance typeDeviationIC (price : Price) (i : Fin 2) : (problem price i).HasTypeDeviationIC where
  typeDeviationIC v valid w validReport := by
    change (problem price i).payoff v (strategy price w) ≤
      (problem price i).payoff v (strategy price v)
    rw [payoff_on_strategy price i v w validReport, payoff_on_strategy price i v v valid]
    nlinarith [sq_nonneg (v - w)]

theorem lowest_utility (price : Price) (i : Fin 2) :
    (problem price i).U (problem price i).lowestType = baseline price ^ 2 := by
  change (problem price i).U 0 = _
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, zero_add] using
    utility_eq price i 0 (by norm_num)

theorem interior_utility (price : Price) :
    (problem price 0).U (problem price 0).lowestType =
      (model price).K_linear (strategy price) ^ 2 / (4 * (model price).α_coeff) := by
  rw [lowest_utility, K_eq_neg_two_baseline]
  change baseline price ^ 2 = (-2 * baseline price) ^ 2 / (4 * 1)
  ring

/-- Each actual price-indexed mechanism satisfies the native interior-strategy contract. -/
theorem interior_strategy (price : Price) :
    (model price).IsInteriorRegimeStrategy (strategy price) 0 where
  measurable := strategy_measurable price
  strictMonoOn := strategy_strictMonoOn price
  typeDeviationIC := typeDeviationIC price 0
  K_neg := K_neg price
  lowestTypeUtility := interior_utility price

/-- The family is Bayesian Nash under the unchanged actual type law. -/
theorem strategy_isBNE (price : Price) :
    (model price).toAuction.bayesianGame.IsBNE (model price).typeLaw
      ((model price).toAuction.bidStrategy (strategy price) (strategy_measurable price)) :=
  (interior_strategy price).isBNE (model price)

end MathEconLib.Examples.AllPurchase.UniformPriceFamily
