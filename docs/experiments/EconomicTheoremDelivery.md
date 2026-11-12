# Theorem delivery on the selected economic components

Collect validated items on `codex/experiment-economic-building-blocks` and keep
each delivery on a named child branch. These are theorem deliveries; an
architecture experiment is reopened only when a concrete consumer exposes a
new competing design or failure.

## Delivery 01: interior incentives against original bids

- **Baseline:** `6417b38`, Lean/Mathlib 4.35.0; child
  `codex/economic-delivery-01-interior-bid-coverage`.
- **Source check:** the local task notes still list the auction-profit and
  welfare bridges as outstanding. Current `OptimalPricing` and
  `WelfareDecomposition` already implement those bridges; the latest discussion
  on [issue 46](https://github.com/matheconlib/matheconlib/issues/46) points to
  their implementation. Preserve the user-owned notes and use actual source
  coverage when choosing the next theorem.
- **Target:** the existing `IsInteriorRegimeStrategy` compares only prescribed
  report bids. Prove that its actual quadratic cost and highest-bid allocation
  also reject every original real-valued bid, including negative and off-range
  bids. Derive needed continuity from existing hypotheses.
- **Reuse:** ordinary report-coverage composition, native allocation bounds,
  quadratic-cost domination and the existing single-parameter IC owner. Keep
  allocation and cost hypotheses explicit. The unused-subsidy control from the
  component experiments continues to refute an unrestricted report-to-action
  implication.
- **Consumer:** the existing two-uniform-bidder auction already has an
  independent explicit all-bid proof. Apply the general theorem using its
  report-IC/interior certificate, without using that all-bid proof as a premise.
- **Focused result:** `IsInteriorRegimeStrategy.hasUniversalIC` certifies every
  real bid at the representative bidder; `hasUniversalIC_at` transfers that
  conclusion to every identical bidder. No extra continuity, density or type-
  sign assumption is added. The reusable quadratic coverage theorem works for
  all real true types and does not assume interior `K < 0`.
- **Common mathematics:** atomless CDF continuity is independent of auctions;
  all-pay continuity and native outside-range allocation bounds supply the
  auction facts. The existing interval-bound proof moves to its lowest native
  owner and is reused instead of duplicated.
- **Consumer integration:** the uniform two-bidder prize-aware best-response
  theorem now uses the general interior certificate. Its original direct
  all-bid proof stays in place, and its report-IC/interior certificate does not
  use that direct proof as a premise.
- **Focused validation:** `lake --iofail build
  MathEconLib.Auction.AllPurchase.OriginalBidIC` passes (9,094 jobs); the existing
  `MathEconLibExamples.AllPurchase.UniformTwoBidder` target also passes strictly
  (9,105 jobs). Semantic review checks endpoint ties, original-bid domains,
  continuity, payment integrability and the all-bidder transfer.
- **Complete validation:** complete and explicit builds of all 289 authored
  modules pass (9,339 jobs). The kernel audit checks 6,238 declarations using
  only standard axioms; all-source token checks and re-elaboration of the 11
  changed Lean files report zero violations. Changed implementation/example
  files pass warning-as-error and line-length checks. Header, generated-import
  and native BIC arithmetic checks pass. Existing unrelated upstream diagnostic
  output remains visible.
- **Upstream refresh:** fork `main` advances to `4afb0d5`, whose only change is
  removal of obsolete `.claude` instructions. Merge that update into the item
  branch and verify all 289 audited Lean source hashes remain unchanged;
  dependency configuration and toolchain also remain unchanged.
- **Status:** complete. The supplied interior certificate now covers all real
  original bids, and the existing concrete consumer uses it. No new equilibrium-
  existence, ex-post DSIC, ex-ante BNE or cross-price family claim is part of
  this delivery.

## Delivery 02: Bayesian equilibrium under the actual type law

Package the resulting pointwise original-bid comparisons as ex-ante BNE under
the actual auction type law. Reuse native conditional beliefs and averaging;
first prove the interim payoff identity for a nonidentity bid strategy and the
realized-payoff measurability/integrability guards. Constant-bid optimality alone
does not justify skipping those obligations for type-dependent deviations.

- **Baseline:** `4479817`; child
  `codex/economic-delivery-02-bayesian-equilibrium`.
- **Target:** native `BayesianGame.IsBNE` for the common strategy in the
  mechanism-induced game, under `Auction.typeLaw`. This quantifies all admitted
  measurable type-dependent unilateral strategy changes.
- **Guards:** prove conditional fixed-bid payments are integrable, the actual
  payoff is jointly measurable, and incumbent realized utility is integrable.
  Bounded realized types and monotone measurable bids provide the needed
  boundedness; first moments alone do not justify products of random bids.
- **Consumer:** the interior original-bid certificate from Delivery 01, then
  the specified uniform two-bidder example. Keep the original action space and
  standard integrability-filtered BNE convention.
- **Native result:** the generic auction bridge identifies actual conditional
  utility with `q_strat`/`p_strat` for a nonidentity common bid strategy and uses
  the existing conditional-averaging theorem. The joint type law, true values,
  signed transfers, incumbent guard and integrability-filtered strategy-deviation
  convention are retained.
- **Model guards:** linear scarcity gives measurable raw payments and integrable
  fixed-bid payments. A strengthened bounded-strategy theorem lives in
  `Auction.IdenticalTypes`; the old first-moment theorem is its corollary. Bounded
  factors justify realized-utility products without an L1-times-L1 shortcut.
- **Focused validation:** generic bridge passes strictly (3,141 jobs), the
  interior native BNE target passes strictly (9,097 jobs), and the uniform
  two-bidder example now proves `strategy_isBNE` (9,108 jobs). Semantic review
  confirms the actual prior, simultaneous interval comparisons, arbitrary
  admitted type-dependent deviations and all integrability guards.
- **Numerical consumer:** `UniformTwoBidderBayesianPayoff` computes each bidder's
  actual ex-ante utility as `13/36` and bounds every admitted measurable
  unilateral strategy profile by that value. It uses native interim averaging,
  the actual marginal pushforward and the existing uniform second moment. Its
  focused strict target passes (9,109 jobs).
- **Complete validation:** complete and explicit builds of all 293 authored
  modules pass (9,343 jobs). The project-wide kernel audit checks 6,261
  declarations using only standard axioms; all-source token scanning and
  re-elaboration of all 10 changed Lean files report zero violations. Changed
  implementation/example files pass strict warning/line-length checks. Header,
  generated-import and native BIC arithmetic checks pass. Dependency pins,
  toolchain and the standard deviation-integrability convention are unchanged.
- **Status:** complete. The general result assumes a supplied interior
  certificate; the concrete uniform model supplies one and its actual native
  BNE payoff is computed. No arbitrary-price existence claim or change in
  equilibrium semantics is introduced.

## Delivery 03: equilibria across posted prices

- **Baseline:** `4a1f42c`; child
  `codex/economic-delivery-03-price-indexed-equilibria`.
- **Target:** construct actual repriced auctions, retaining allocation, scarcity
  and the type law while changing transfers. For two independent uniform
  bidders, construct a native BNE at every price in `(0, 5/2)` and compare actual
  seller profits across these equilibria.
- **Reuse:** native interior certificates, original-action IC, conditional
  averaging and the established profit identity. Compare auctions with common
  economic primitives explicitly; no new family structure is needed.
- **Scope:** the positive-price interior regime and zero production cost. A
  boundary-regime comparison needs its own equilibrium existence proof.
- **Focused result:** repricing changes each payment by the price difference
  times own purchases and preserves the actual joint type law. The affine
  strategy `(5 - 2p)/6 + v/2` supplies native report IC and an interior
  certificate, hence original-action IC and native BNE throughout `(0, 5/2)`.
  Its focused strict target passes (9,112 jobs). The generic two-auction profit
  comparison also passes strictly, conditional on supplied interior certificates
  and equality of the scarcity intercept, slope and distribution-based moment.
- **Economic consumer:** expected aggregate purchases are `2(4-p)/3`, actual
  seller profit at cost zero is `2p(4-p)/3`, and the actual price-two member
  uniquely maximizes profit in the family at `8/3`. The gap is
  `(2/3)(p-2)^2`. All three generic two-auction comparison results are consumed;
  existence at the maximizing price is supplied by the family, rather than
  assumed from a polynomial optimum. Price two recovers the original auction
  and strategy. The focused strict consumer target passes (9,113 jobs).
- **Complete validation:** complete and explicit builds of all 298 authored
  modules pass (9,348 jobs). The kernel audit checks 6,335 declarations with
  only standard axioms. All-source forbidden-token scanning and re-elaboration
  of all eight changed Lean files report zero violations; the source pass
  finds no discarded declarations. Changed implementation/example files pass
  strict warning and line-length checks. Header, generated-import and native
  BIC arithmetic checks pass. Existing unrelated upstream diagnostics remain
  visible. A fresh upstream fetch retains `4afb0d5`; dependency pins and
  toolchain remain unchanged.
- **Status:** complete. Actual equilibria and the unique zero-cost profit
  maximizer are constructed within the specified interior-price family.
  Two supplied interior auctions can also be compared from their common
  primitives. Boundary regimes and other equilibrium families remain outside
  this delivery's conclusions.

## Delivery 04: the zero-baseline endpoint equilibrium

- **Baseline:** `11feabe`; child
  `codex/economic-delivery-04-boundary-equilibrium`.
- **Target:** actual native BNE at price `5/2`, with purchases `v/2`, zero
  lowest-type utility and `K=0`. Prove that this strategy does not satisfy the
  strict interior certificate, and compare its actual seller profit at cost
  one with every constructed interior-family member.
- **Reuse:** factor the existing original-action coverage proof into an auction
  operation taking continuity and the cost-minimizing lowest bid explicitly.
  Derive those premises from interior certificates for existing clients; supply
  them directly at the endpoint. Keep native equilibrium and integrability
  semantics and the actual repriced mechanism.
- **Scope:** a single boundary endpoint and its comparison with the constructed
  interior family. A global boundary-regime existence theorem is separate.
- **Focused result:** the generic auction coverage operation and the existing
  interior specialization pass strictly (9,094 jobs). The actual repriced
  endpoint supplies native boundary utility, all-real-bid IC and BNE, and proves
  `not_interior` for every bidder. Its strict target passes (9,112 jobs).
- **Economic consumer:** the endpoint's actual aggregate quantity is one and
  its actual profit at production cost one is `3/2`. Every constructed interior
  family member earns strictly less at that cost, with exact gap
  `(2/3)(p-5/2)^2`. The scalar optimum is connected to the independently
  evaluated endpoint, without an interior certificate there. The focused
  strict profit target passes (9,115 jobs). The interior family's quantity also
  gives its explicit profit formula at every production cost; the old zero-cost
  result is a specialization.
- **Complete validation:** complete and explicit builds of all 300 authored
  modules pass (9,350 jobs). The kernel audit checks 6,367 declarations using
  only standard axioms. All-source forbidden-token scanning and re-elaboration
  of all five changed Lean files report zero violations; no discarded
  declarations occur in the source pass. Changed implementation/example targets
  pass strict warning and line-length checks. Header, generated-import and
  native BIC arithmetic checks pass. Existing unrelated upstream diagnostics
  remain visible. A fresh upstream fetch retains `4afb0d5`; dependency pins
  and toolchain remain unchanged.
- **Status:** complete. The actual endpoint is native Bayesian Nash and lacks
  the strict interior certificate. Its profit at cost one strictly dominates
  every constructed interior-family equilibrium at that same cost. The result
  concerns this equilibrium selection and does not classify other prices,
  strategies or boundary regimes.

## Delivery 05: a positive-cost boundary equilibrium with nonnegative bids

- **Baseline:** `f686c0f`; child
  `codex/economic-delivery-05-nonnegative-boundary`.
- **Target:** two independent uniform bidders use
  `β(v) = (sqrt(1+v^2)-1)/2`. Let `μ` be its actual mean purchase and post the
  positive price `4-μ`, so the native marginal cost coefficient is exactly one.
  Prove Bayesian equilibrium in the actual mechanism restricted to nonnegative
  actions, under the unchanged actual type law.
- **Reuse:** native report IC, continuous payoff coverage on the nonnegative
  action set, mechanism action comaps, conditional averaging and the existing
  measurable/integrable linear-scarcity guards. The real-valued bidder view
  remains available, with feasible deviations stated explicitly.
- **Scope:** one actual positive-`K` boundary equilibrium. This is theorem
  delivery after the closed building-block experiments, not a claim about all
  boundary prices, unrestricted signed-bid BNE or uniqueness.
- **Focused result:** nonnegative quadratic-cost report coverage and its
  auction specialization compile. A generic conditional-payoff identity lives
  at the Bayesian game layer (3,094-job target); the restricted auction BNE
  bridge (3,144 jobs) reuses the actual prior and native averaging. Its
  linear-scarcity wrapper (3,151 jobs) derives the measurable/integrable guards.
  The existing real interim identity's all-real fixed-payment integrability
  premise remains explicit, even for restricted actions.
- **Concrete equilibrium:** `PositiveKBoundary` builds (9,116 jobs). The
  actual mean satisfies `0 ≤ μ ≤ 1/2`, hence the posted price lies in `[7/2,4]`;
  its actual `K` is one. Native report IC, zero lowest-type utility and
  nonnegative original-bid IC yield native Bayesian equilibrium under the
  original type law against all admitted measurable nonnegative deviations.
- **Status:** in progress.

## Subsequent action-domain control

MEC-015 completes the proposed positive-`K` domain control. At price four and a
mass-one zero-value prior, the actual negative-bid gain excludes the real zero
strategy from native BNE. The included zero strategy is native BNE under typed
nonnegative actions, with the same transfers and prior; every payoff in the
comparison is integrable. The native mechanism action comap supplies the
restriction. The [experiment log](EconomicBuildingBlocksLog.md) records its
full gate. This resolves the domain competition without classifying all
boundary-price equilibrium families; that larger classification remains
ordinary theorem delivery on an explicitly chosen action domain.
