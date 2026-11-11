# Economic building-block experiment log

This log belongs to the fork-local investigation described in
`EconomicBuildingBlocks.md`. Item identifiers here are independent of the
earlier GameTheory experiment ledger.

## MEC-001: native demand regularity and a shared maximizer operation

- **Date / status:** 2026-11-12; reserved, in progress.
- **Question:** Can the canonical feasible-maximizer graph theorem be used by
  MathEconLib's existing `utilityChoice` on genuinely changing budgets without
  copying mathematics, changing demand semantics or adding a shared problem
  record? Does strict positivity of prices permit zero wealth, where the
  earlier positive-wealth recovery theorem is insufficient?
- **Alternatives:** native budget recovery plus a transient import of the
  canonical mathematical operation; a new demand record, repeated argmax proof
  or a premature permanent cross-library dependency.
- **Representative slice:** finite commodity bundles, continuous strictly
  positive price vectors and continuous nonnegative wealth including zero;
  continuous utility and all tied maximizers. Prove budget lower
  hemicontinuity and closed demand graph through existing `utilityChoice`.
- **Kill conditions / controls:** preserve the native nonnegative budget and
  all ties; do not replace demand by a selector, require positive wealth
  without testing the admitted zero case, or conflate graph closedness with
  existence. A zero-income/free-good boundary must reject dropping all
  recovery conditions. The transient consumer must check matching dependency
  pins and audit its materialized Lean source without weakening project checks.
- **Artifacts / baseline:** child branch
  `codex/experiment-economic-item-01-parametric-demand`, collecting checkpoint
  `f61ec82` over upstream `b0c6f35`; committed reproduction templates and
  commands will accompany the result. The GameTheory mathematical owner remains
  canonical during the experiment; no package ownership is frozen here.
