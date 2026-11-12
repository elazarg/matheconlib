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

## Next dependency path

Package the resulting pointwise original-bid comparisons as ex-ante BNE under
the actual auction type law. Reuse native conditional beliefs and averaging;
first prove the interim payoff identity for a nonidentity bid strategy and the
realized-payoff measurability/integrability guards. Constant-bid optimality alone
does not justify skipping those obligations for type-dependent deviations.
