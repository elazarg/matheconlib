# Economic building-block experiments

This is a fork-local design experiment, collecting on
`codex/experiment-economic-building-blocks`. Each measured item uses a child
branch; successful evidence is merged into the collecting branch. No new
worktree is created and existing sibling checkouts are left alone.

## Current result

The supplied comparisons and the follow-up supporting-form, blocking, demand,
information, calibration, law-preference and provenance paths have completed
their initial gates (283 modules and 6,224 audited declarations). Four native
theorem deliveries then exercised the selected components through actual
Bayesian equilibria and profit comparisons. The final action-domain,
admissibility and atomic/nonatomic controls close the identified competition
queue. The experiment-closure gate covers 304 modules and 6,478 audited declarations;
[the closure record](BuildingBlockClosure.md) states the outcomes, validation
and reopening conditions.
Useful expressiveness and actual reuse governed selection; increased proof
length was treated as a cost rather than a veto.

The [findings and component map](EconomicBuildingBlocksFindings.md) describe
what was selected, the proved limits and the empirical stopping point. The
[evaluation criteria](ComponentEvaluation.md) cite the design guidance used.
The [log](EconomicBuildingBlocksLog.md) preserves original questions and failed,
narrowed and supporting observations. The working guarded-foundation and shared-
demand alternatives remain on named evidence branches. Basic abstractions remain
replaceable when another concrete consumer discriminates between designs.
Subsequent native consumers and their validation are recorded separately in
[the theorem-delivery ledger](EconomicTheoremDelivery.md).

## Starting point

On 2026-11-12 the local fork and its `origin/main` were fast-forwarded to
upstream `b0c6f35`. The preceding local checkout was 93 commits behind. Lean
and Mathlib remain pinned to 4.35.0. This baseline already includes explicit
comparison and candidate-validity equilibrium APIs, supplied-utility mechanism
and Bayesian views, weak preference/maximizer interfaces, and finite Afriat
rationalization through the canonical choice carrier.

The root `AbstractionAnalysis.md`, `SurveyEvidence.md` and `Experiments.md` are
user-supplied starting hypotheses. Their revised snapshots are retained under
`sources/`; earlier versions remain in git history. The survey distinguishes
upstream main from the separate simulations branch. The proposed experiments
ask whether `EquilibriumProblem` earns its place as an internal building block
or primarily supplies client vocabulary. Either answer must be allowed by the
measurements; the proposed hierarchy is not an implementation checklist.
The prior GameTheory investigation selected independent mathematical
operations and preserved domain-owned semantics; its final record is
[D92](https://github.com/elazarg/GameTheory/blob/9f74339e/docs/decisions/D92-economic-extraction-boundary.md).

The original additional source is
[the supplied artifact](https://claude.ai/artifact/QGxkUNzPsXB8QPFASJ2afW#c4750e5e-ce41).
Its public URL returns an application shell and its content endpoint refuses
unauthenticated access. The user supplied the revised local Markdown files
instead; these supersede the need to retrieve the artifact.

The governing defaults remain `DESIGN.md`, `CONTRIBUTING.md` and the actual
current APIs. Local experimental branches may replace basic abstractions,
including open design choices, as extensively as useful. Existing APIs are a
comparison baseline, not a veto. Evidence selects what to retain or recommend;
semantic differences must be stated rather than counted as free simplification.

## Initial experiment order after the revised inputs

1. **E4: strong Nash and local comparability.** Generalize the theorem on a
   real core branch, retain a linear-order specialization, and test vector
   payoffs and incomparability.
2. **E2: infinite-gain deviation.** Build the actual two-player probability
   model and measure guard handling. Distinguish the documented integrable-only
   convention from an intentional extended-value alternative. Existing
   nonintegrable-deviation controls must be acknowledged.
3. **E1 and E3: the deciding comparisons.** Implement both actual foundation
   routes: revelation through maps versus direct reasoning, and a shared
   guarded operation with native specializations versus the existing owners.
   Charge all constructions, changed hypotheses, proof lines and second uses.
4. **E5, then E6 if still useful.** Test composed reductions against repeated
   hypotheses, then law-preference mixed equilibrium if the architectural
   question remains unresolved. The simulations branch is a separate pinned
   source, never silently substituted for main.

The initial demand probe was reserved before the revised files arrived and
deferred before compilation while comparing the record routes. It was later
resumed and completed as MEC-009. Its original hypothesis and kill conditions
remain in the log; the initial deferral was not a refutation.

## Resumed extraction consumer

Test regularity of demand on changing price/wealth budgets through the existing
`RevealedPreference.utilityChoice`. Upstream's representation and observed
attainment results do not establish a closed graph for changing feasible menus.

The later item connects native nonnegative bundles and expenditure to
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
- Track incumbent validity, allowed deviations, ties, information, transfer
  signs and evaluation domains. For equal-semantics comparisons preserve them;
  intentional changes are valid experimental alternatives and must be named.
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

Select later variants from measured evidence and the revised starting files.
Changing a foundation locally needs no further permission. Recommending it as
the resulting design requires convincing comparative and semantic evidence.

## Corrections discovered against current sources

Build environment note: the fork initially lacked much of the pinned compiled
dependency cache. Local Lake `package-overrides.json` reuses the sibling's
third-party package locations only after checking all nine manifest revisions
match and their tracked sources are clean. The toolchain remains 4.35.0 and
`lake-manifest.json` is unchanged. This is local cache reuse, not a dependency
on GameTheory's authored library or a design assumption. A separate checkout
can reproduce the commands with the ordinary matching Mathlib cache instead.

- E2's inventory understates existing coverage: `Integrability.lean` already
  tests filtered nonintegrable deviations and a deviation whose opponent alone
  becomes nonintegrable. Positive infinite gain remains a distinct control;
  it is not the first deviation-integrability test or automatically a bug.
- E1's natural map is `GameComorphism`: report changes map to original action
  changes, and equilibrium pulls back. Requiring an opposite-direction
  morphism would unfairly charge the record route for unavailable preimages.
  The simulations branch already contains a short revelation application;
  it is a pinned comparison source, not a new result on current main.
- E3 must check equivalence rather than assume definitional identity: a bare
  score maximum has no feasibility or evaluation guard; equilibrium validity
  applies only to incumbents and must survive empty judge types. These are
  testable obligations for rival foundations, not reasons to forbid them.
- E5's reduction API belongs to the separately pinned simulations branch.
  E6 may reuse an outcome law as the current record's value carrier, so that
  fact alone cannot discriminate between the two architectural hypotheses.
