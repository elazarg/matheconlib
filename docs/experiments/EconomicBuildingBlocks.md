# Economic building-block experiments

This is a fork-local design experiment, collecting on
`codex/experiment-economic-building-blocks`. Each measured item uses a child
branch; successful evidence is merged into the collecting branch. No new
worktree is created and existing sibling checkouts are left alone.

## Starting point

On 2026-11-12 the local fork and its `origin/main` were fast-forwarded to
upstream `b0c6f35`. The preceding local checkout was 93 commits behind. Lean
and Mathlib remain pinned to 4.35.0. This baseline already includes explicit
comparison and candidate-validity equilibrium APIs, supplied-utility mechanism
and Bayesian views, weak preference/maximizer interfaces, and finite Afriat
rationalization through the canonical choice carrier.

The root `AbstractionAnalysis.md` and `SurveyEvidence.md` are user-supplied
historical proposals, including references to an older simulations branch.
Their unchanged snapshots are retained under `sources/`. They motivate
questions; their proposed hierarchy is not an implementation checklist.
The prior GameTheory investigation selected independent mathematical
operations and preserved domain-owned semantics; its final record is
[D92](https://github.com/elazarg/GameTheory/blob/9f74339e/docs/decisions/D92-economic-extraction-boundary.md).

Claude's additional source is
[the supplied artifact](https://claude.ai/artifact/QGxkUNzPsXB8QPFASJ2afW#c4750e5e-ce41).
Its public URL currently returns an application shell and its content endpoint
refuses unauthenticated access. Its content has not been reviewed or adopted;
the user has been asked for the relevant text while independent work proceeds.

The governing defaults remain `DESIGN.md`, `CONTRIBUTING.md` and the actual
current APIs. No experiment changes those defaults by silently redefining an
economic concept.

## First discriminating consumer

Test regularity of demand on changing price/wealth budgets through the existing
`RevealedPreference.utilityChoice`. Upstream's representation and observed
attainment results do not establish a closed graph for changing feasible menus.

The first item should connect native nonnegative bundles and expenditure to
budget lower hemicontinuity and closed feasible-maximizer graphs. Include zero
wealth under strictly positive prices, which is admitted by the current
dataset model. Test tied demand and the zero-price/zero-wealth failure. Keep
closedness distinct from existence, uniqueness, compactness and identification.

The already validated GameTheory `Math.ParametricOptimality` theorem is a
candidate shared operation. A transient consumer may import its canonical
compiled module with matching dependency pins. That checks cross-library use
without copying its implementation, adding a permanent dependency or freezing
a new package owner. The exact source, imports, commands and proof-integrity
checks must be reproducible. Promotion requires a separate ownership decision.

## Admission and stopping rules

- Begin with a named native consumer and a hypothesis that a small hostile
  example can refute. Reserve an entry in `EconomicBuildingBlocksLog.md` before
  starting the experiment.
- Search current MathEconLib and Mathlib by statement shape. Reuse new upstream
  owners rather than porting work they already subsume.
- Preserve incumbent validity, allowed deviations, ties, information, transfer
  signs and evaluation domains. Distinguish stronger convenience assumptions
  from constitutive semantics.
- Compare direct hypotheses and existing transformations before introducing
  records, typeclasses or another probability abstraction. A successful
  negative result may leave every public definition unchanged.
- Serialize integration and compilation. Keep temporary materializations out
  of the authored Lean tree and explicitly audit them; do not weaken the
  repository's orphan or proof-integrity checks to accommodate experiments.
- Record focused strict builds, the complete project checks and actual scope.
  Commit and push to the fork frequently; do not publish to upstream.
- Stop when named consumers reuse established operations with local hypotheses
  and remaining tasks are theorem delivery or economic accounting. Reopen for
  demonstrated missing operations, duplicated semantics or excessive transport.

After the demand experiment, select the next item from measured evidence and
Claude's supplied content when available. No later hierarchy or broad rewrite
is pre-approved by this plan.
