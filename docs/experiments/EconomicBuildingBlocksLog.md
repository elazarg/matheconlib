# Economic building-block experiment log

This log belongs to the fork-local investigation described in
`EconomicBuildingBlocks.md`. Item identifiers here are independent of the
earlier GameTheory experiment ledger.

## MEC-001: native demand regularity and a shared maximizer operation

- **Date / status:** 2026-11-12; deferred before compilation after revised experiment inputs.
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
- **Outcome:** not run. A native recovery draft is retained locally, but no
  build, measurement or conclusion is claimed. The user's revised
  `Experiments.md` makes the record-versus-operations comparison the first
  priority. Preserve this reservation and return only if extraction becomes
  the useful next question.

## MEC-002 / source E4: strong Nash with local comparability

- **Date / status:** 2026-11-12; complete for the focused slice, supporting local comparability.
- **Question:** Does strong-Nash equivalence with absence of unanimous strict
  gains require a globally linear reward order, or only actual comparisons
  between incumbents and changed participants' alternatives?
- **Alternatives:** the current global `LinearOrder` theorem; a `Preorder`
  theorem with comparison hypotheses restricted to actual changed players.
  This tests the invariance principle rather than deciding record ownership.
- **Representative slice:** change the core theorem on the item branch, make
  its existing linear version a specialization, and use a two-player
  componentwise vector-payoff game. Include an incomparable-payoff rejection
  control, so dropping comparison entirely cannot pass.
- **Kill conditions:** keep the existing strong-Nash meaning and quantify the
  same joint replacement for every changed player; do not quietly replace weak
  rejection by absence of strict gain on incomparable rewards. Count the added
  hypothesis and actual consumer proof, not only the core theorem.
- **Artifacts / commands:** core
  `MathEconLib/GameTheory/Strategic/Basic.lean`, consumer and rejection control
  `MathEconLibTest/GameTheory/StrongNashComparability.lean`, imported by the
  regenerated `MathEconLibTest.lean`; child
  `codex/experiment-economic-item-02-local-strong-nash` over `48ba448`.
  `lake --iofail build MathEconLibTest.GameTheory.StrongNashComparability`
  passes 866 jobs. Import regeneration/check and copyright checks pass.
- **Measurements:** the new generic theorem uses 17 nonblank lines; the whole
  fixture uses 75 nonblank lines excluding block comments. The linear-order
  proof is a one-line specialization, as its old proof was one line. No source
  compression or elaboration-performance advantage is claimed.
- **Observations:** a two-player coordination game with product-ordered real
  vector rewards has an ordinary equilibrium defeated by a genuine joint
  change, while the successful profile consumes the new local theorem.
  A one-player crossing-vector replacement has no strict gain but violates
  strong Nash; the proposed equivalence without comparability is explicitly
  refuted. No global totality, finite-player or nonempty-player hypothesis is
  added to the theorem.
- **Integrity / outcome:** compiled axiom audit checks 88 owned declarations
  across the core and fixture, with only `propext`, `Classical.choice` and
  `Quot.sound`; source elaboration checks report no violations. The source
  checks contain no anonymous examples, which are separately covered by the
  compiled named-declaration audit. Retain the core generalization. This is
  hypothesis-locality evidence and is neutral on records versus operations.
  Complete project validation remains a gate for the investigation.

## MEC-003 / source E2: an infinite positive deviation

- **Date / status:** 2026-11-12; semantic control complete; certificate-size hypothesis still unproved.
- **Question:** What does the current finite-integrable-deviation convention
  assert when an excluded unilateral move has infinite nonnegative gain?
  Does separating evaluation-domain information reduce actual certificate work,
  rather than merely move the same hypotheses?
- **Alternatives:** current finite-Bochner semantics and its existing filter;
  explicitly separated evaluation guards under the same semantics; an
  extended-value convention is a distinct admissible experimental alternative,
  not silently equated with either of those.
- **Representative slice:** two players choose Bool and a natural number.
  The first stays for payoff zero or chooses `2^(n+1)`; the other receives zero
  and randomizes geometrically. Prove an admitted equilibrium under the native
  definition and an excluded own deviation with nonnegative integral top.
- **Kill conditions:** prove equilibrium against every admitted mixed
  deviation, not merely pure deviations. State infinite gain as a nonnegative
  integral, since the real Bochner integral totalizes outside its domain.
  Acknowledge current nonintegrable-deviation and opponent-only controls; charge
  product-law and arbitrary-deviation proofs in the size measurement.
- **Baseline / artifacts:** collecting `1d3750a`; child
  `codex/experiment-economic-item-03-infinite-gain`. The original 40–60 line
  estimate remains a hypothesis to measure, not a budget to satisfy by hiding
  infrastructure.
- **Artifacts / commands:** `MathEconLibTest/GameTheory/InfiniteGain.lean`,
  wired into the regenerated test umbrella. `lake build
  MathEconLibTest.GameTheory.InfiniteGain` passes 3,051 jobs. The authored
  fixture also passes `lake env lean '-DwarningAsError=true'` independently.
  The strict whole-target command replays upstream's pre-existing deprecated
  `stdSimplex` warning in `ForMathlib/ProbabilityMeasure.lean`; this warning is
  reported separately rather than suppressed or attributed to the experiment.
- **Observations:** all independent mixed deviations are covered. Any positive
  probability of accepting the gamble yields infinite nonnegative integral
  under the actual product law; integrability forces that mass to zero, so
  every admitted deviation has payoff zero. The native incumbent is a mixed
  equilibrium; its pure accepting deviation is excluded and its real-valued
  Bochner integral totalizes to zero.
- **Alternative convention:** the same existing `EquilibriumProblem` with
  law-valued rewards and an explicit nonnegative-integral comparison admits
  every unilateral replacement and rejects this incumbent. Payoffs here are
  nonnegative, and the incumbent is valid under both conventions; the verdict
  difference is therefore not a hidden change in incumbent admissibility.
  No new equilibrium carrier is needed to express the alternative. This is
  an intentional semantics change, not an equivalent cheaper guard factoring.
- **Measurements:** 192 nonblank lines excluding block comments for the
  complete model, product-law/infinity argument, all-deviation proof and
  alternative convention. The 40–60 line prediction was not supported once
  infrastructure was charged. No timing advantage is claimed.
- **Integrity / interpretation:** compiled axiom checks cover 66 owned
  declarations with only the three standard axioms, and source elaboration
  reports no violations. Independent review accepts the all-deviation and
  finite/extended distinctions. Existing negative-gamble and opponent-only
  integrability controls remain in place. This establishes the evaluation
  boundary and expressiveness of the current record. It does not demonstrate
  a certificate-size reduction; paired E1/E3 measurements must still test that
  hypothesis without changing the accepted deviations or candidate guards.

## MEC-004 / source E1: Bayesian revelation through records and direct lifts

- **Date / status:** 2026-11-12; focused comparison complete.
- **Question:** On the same native indirect mechanism, prior and measurable
  strategy, is revelation better served by the existing action-translation
  comorphism or direct measurable-deviation lifting? Does the literal same
  certificate earn a second use?
- **Alternatives:** `BayesianGame.comapActionsComorphism` and its pullback
  operations; direct payoff/integrability/deviation reasoning. Compare the
  natural comorphism direction, not an artificially stronger lifting morphism.
- **Representative slice:** arbitrary supplied full-consequence utility and
  the same candidate/deviation integrability convention; exact BNE and a second
  explicit-comparison equilibrium using the same certificate. A finite
  posted-price mechanism has an unused third action, a non-surjective indirect
  strategy, a fair prior over two types, and actual applications of both routes.
- **Kill conditions / measurement:** identical scopes and assumptions, all
  measurable lifts and helpers charged, no private-value, quasilinear or
  surjectivity assumptions added to the generic result. Distinguish installed
  infrastructure, cold construction, shared semantics and marginal proofs.
  The second comparison use is not falsely labeled the same DSIC certificate.
  The pinned simulations-branch proof is prior evidence, not newly authored.
- **Baseline / artifacts:** collecting `b2dc746`; child
  `codex/experiment-economic-item-04-bayesian-revelation`. Route and concrete
  application files will remain directly compiled under the test umbrella.
- **Artifacts / validation:** `MathEconLibTest/GameTheory/BayesianRevelation.lean`
  and `RevelationConsumer.lean`; `lake build` on both targets passes 3,059 jobs.
  Both authored files pass independent warning-as-error and long-line checks.
  The build replays only the previously recorded upstream `stdSimplex` warning.
  Compiled integrity checks cover 50 declarations with only the three standard
  axioms; source elaboration checks cover discarded examples separately.
- **Measurements:** excluding block comments, the generic file has 65 nonblank
  lines and the economic consumer 64. Ordinary/comparison record clients use
  3/4 lines including signatures. The direct comparison theorem uses 8, and a
  factored ordinary client reusing it uses 5; the separate unfactored ordinary
  proof uses 7. Thus reuse is available to both alternatives. The installed
  `comapActionsComorphism` constructor itself costs 12 lines, in addition to
  the general comorphism structure and pullback operations; these are not free
  in a cold comparison. Both routes share the native `Strategy.mapActions`.
  The direct route's opponent-agreement helper costs 10 lines; shared truthful,
  lift and payoff helpers are retained explicitly. No timing win is claimed.
- **Observations:** the generic statements have the same utility, prior,
  candidate validity and own-deviation integrability assumptions. They require
  neither surjectivity nor quasilinear/private-value utility. The monetary
  consumer checks both types against all three actions, proves the unused
  action has no strategy preimage, and applies both routes. The literal same
  report comorphism transports ordinary and arbitrary explicit comparisons;
  concrete error-tolerant clients apply this second theorem. Their source
  bound follows from exact BNE, so this is not an approximate-only existence
  example. The concrete mechanism has one player; the generic result handles
  arbitrary opponents without changing them.
- **Interpretation / next:** existing comorphisms earn marginal proof reuse
  here, but this does not establish their cold-cost superiority or a universal
  equilibrium hub. Factoring the direct theorem also reuses work. Part of its
  remaining ordinary-client cost converts the separately defined ordered and
  explicit-comparison judgements; test canonical specialization independently
  before attributing that cost to records versus mathematical operations.
  Retain both compiled routes as evidence. Whole-project integration remains
  the investigation's final gate.

## MEC-005 / source E3: who owns optimality proofs?

- **Date / status:** 2026-11-12; reserved, in progress.
- **Question:** Does a Mathlib-only guarded optimality operation earn ownership
  of reusable proofs across equilibrium and attained choice, against the best
  native direct/record baseline?
- **Alternatives:** first canonicalize ordered equilibrium as a transparent
  specialization of explicit comparison (independent native control); then
  redefine actual per-player optimality through guarded menu optimality and
  use its coverage theorem in game transport and a native choice contraction.
  Keep both revisions reviewable, including an unsuccessful guarded rival.
- **Representative slice:** existing Bayesian revelation clients, morphism
  transport, native attained-bundle contraction/IRC, invalid deviation targets,
  integrability filters, and an invalid incumbent with no judges.
- **Kill conditions:** no loss of incumbent validity, no added target-validity
  restriction, and no hidden changes to menus or comparisons. Charge all
  bridging lemmas, repaired consumers and the second-use proof. Separate native
  canonicalization gains from gains requiring a mathematical guarded layer.
  A longer or semantically distorted implementation may refute proof ownership
  without refuting the usefulness of the standalone operation.
- **Baseline / artifacts:** collecting `483576e`; child
  `codex/experiment-economic-item-05-optimality-foundations`. Compile serially;
  no worktrees. Initial native transport body is three nonblank lines; attained
  choice contraction body is six. No speed or compression result is assumed.
- **Native control result:** ordered `IsDeviationOptimal` and `IsEquilibrium`
  now transparently specialize their explicit-comparison owners. Both ordered
  map transports reuse the corresponding generic comparison transport. The
  factored direct revelation client drops its two representation conversions
  and becomes a single application, matching the ordinary record client's
  three-line declaration. Core source changes total 13 additions/19 deletions;
  two internal method calls require explicit namespaces after abbreviation.
  No downstream proof repairs are required. A new empty-judge fixture retains
  rejection of an invalid incumbent despite vacuous deviation optimality.
  `lake --iofail build MathEconLib.GameTheory.Equilibrium.Problem` passes;
  complete `lake build` passes 9,302 jobs including API pins, examples and
  tests. Existing upstream warnings/info remain visible. Compiled axiom checks
  cover 189 declarations in the core, validity and revelation controls, with
  only standard axioms; source checks pass. Retain this independent control
  before trying the guarded rival; it already removes duplicated ownership.
- **Guarded rival:** child `codex/experiment-economic-item-05b-guarded-core`
  actually replaces native `IsOptimalWith` by a guarded-menu specialization.
  Both map transports and native attained-choice contraction consume the same
  Mathlib-only coverage operation. Preference maxima and score maxima have
  exact iff bridges; they are not claimed to be definitionally identical to
  their prior definitions. No theorem hypotheses, deviation menus, incumbent
  guards or integrability conventions change. Empty judges and invalid targets
  remain explicit controls.
- **Measured result:** see `OptimalityFoundationComparison.md`. Excluding block
  comments/blank lines, the replacement adds 121 code lines across 18 files,
  including the 59-line leaf, all bridges and downstream repairs. Excluding
  the opening `by`, each explicit map transport body grows from three to seven
  lines; choice contraction grows from five to nine. The initial rough count
  of six choice lines used a different boundary and is corrected here. Actual
  sharing succeeds in two areas without added assumptions, but proof economy
  does not improve against the independently simplified native baseline.
- **Validation / selection:** full `lake build` passes 9,303 jobs, including
  API pins, examples and tests. Focused leaf/core strict builds pass. Compiled
  integrity checks cover 653 declarations across all 17 changed authored
  modules, with only standard axioms. Changed-source elaboration checks pass
  all 18 files, including 25 discarded declarations and zero violations.
  Keep the full alternative on its branch; select native
  canonicalization for collection. This is evidence against forcing this
  guarded representation on these consumers, not against every independently
  useful mathematical operation or future foundational change.

## MEC-006 / source E5: chained dominated-action reductions

- **Date / status:** 2026-11-12; complete, including final integration.
- **Question:** Does a composed simulation shorten two-round and arbitrary
  finite-round equilibrium transport against reusable direct per-round
  equivalences, rather than against duplicated direct payoff arguments?
- **Alternatives:** the six-field `GameSimulation` and composition from pinned
  branch `13f5a84`; native pointwise domination equivalences composed with
  `Iff.trans`. Supply identical global domination witnesses for the paired
  comparison; separately acknowledge the direct theorem's pointwise scope.
- **Representative slice:** a two-player two-action game first eliminates a
  globally dominated row, then a column dominated only after that restriction.
  The lifted final profile is an equilibrium. A bad retained row must fail
  domination and must not lift its final equilibrium.
- **Kill conditions:** preserve all simulation fields, validity, value maps,
  admitted deviations and included-profile scope. Share economic witnesses.
  Give both routes reusable composition/induction; do not compare a full
  certificate against a verdict implication without naming the stronger output.
  Charge the pinned support materialization separately from marginal clients.
- **Baseline / artifacts:** selected native control `ac2024a`; planned child
  `codex/experiment-economic-item-06-chained-reductions`. The old simulations
  branch has diverging foundations; materialize only the required exact source
  slice in a test namespace, with documented proof adaptations. No unrelated
  simulation/error/reflection API is required or silently ported.
- **Artifacts / provenance:** `MathEconLibTest/GameTheory/ReductionSupport.lean`
  materializes the six-field simulation, identity/composition and dominated
  action reduction statements from `Equilibrium/Simulation.lean` and
  `Strategic/Reduction.lean` at `13f5a84`. Its transport proof directly chains
  the same bounds, and its pointwise equivalence directly uses `isNash_iff`;
  these two proof adaptations avoid branch-only comparison APIs. They add no
  hypotheses. `ReductionChains.lean` supplies direct implication/equivalence
  induction and full certificate induction, with equal composite state maps.
  `ChainedReductions.lean` supplies the hostile economic example and both routes.
- **Observations:** the retained row globally dominates the omitted row. The
  retained column dominates only after that restriction; its full-game claim
  is refuted. Both routes consume the literal same global witnesses and prove
  the same included-profile equivalence. Retaining the bad row explicitly
  violates domination; the resulting singleton game's equilibrium is not an
  original equilibrium. Reflection uses the native action comorphism, not a
  nonexistent reflection property of every simulation.
- **Measurements:** 78 nonblank code lines excluding block comments for pinned
  support, 35 for the chain comparison and 115 for the economic fixture. The
  record equivalence uses three lines including its signature, plus two lines
  for each of its two named certificates; direct equivalence uses five. Both
  routes share economic witnesses and native action-comorphism reflection.
  The 60–120 line estimate fits the fixture but not the charged support and
  induction. No timing advantage is claimed.
- **Scope / result:** direct implications and equivalences compose through
  arbitrary finite chains. Full simulations compose too and retain richer
  data: deviator/value maps, deviation witnesses and validity transport. State
  and judge types may change; the generic certificate-chain theorem fixes one
  value preorder, while binary composition supports different value carriers.
  Thus n-round verdict induction is not exclusive evidence for records, and
  the richer certificate is not compared as if it were merely an implication.
  The pointwise direct theorem permits weaker scope than a globally packaged
  simulation; the paired example deliberately gives both the global hypothesis.
- **Validation:** all three focused targets pass `lake --iofail build` (868 or
  fewer dependency jobs). Compiled integrity checks cover 107 declarations
  with only standard axioms. Independent semantic/fairness review passes.
  All three source elaboration checks pass (no discarded examples; the 107
  named declarations are covered by the compiled check). Final integration
  passes as recorded below.

## Selected-branch integration gate

- **Date / source:** 2026-11-12; reduction child `b1e7517`, collected with the
  native optimality specialization. A final fetch confirms both upstream main
  and fork main still point to `b0c6f35`.
- **Build:** regenerated Git-based umbrellas, then complete `lake build` passes
  9,305 jobs including library, API pins, examples and tests. An explicit
  `lake --rehash --no-ansi build` on all 255 authored modules discovered by the
  proof-integrity driver's `discover_sources` also passes 9,305 jobs. This
  includes sources independently of umbrella reachability.
- **Integrity:** `lake env lean --run scripts/CheckProofIntegrity.lean REPORT`
  with that complete module list checks 5,870 declarations in 255 modules:
  only `propext`, `Classical.choice` and `Quot.sound`, zero violations.
  The driver's source-token scan finds zero holes across all 255 sources.
  Source elaboration was checked on the experiment sources at their individual
  gates; the guarded rival additionally checked all 18 changed files, including
  25 discarded declarations. This records project-wide compiled coverage and
  scoped source re-elaboration, not a fresh elaboration of every unchanged file.
- **Repository checks:** `scripts/check-headers.sh` and
  `scripts/update-imports.sh --check` pass. Integrity-checker tests pass 21 cases;
  warning-report tests pass 28. The import-helper harness passes 11 cases under
  WSL using a temporary LF-normalized helper copy, matching the Linux CI input.
  The initial native invocation selected Windows' WSL `bash` with Windows path
  syntax; the Node harness needed Git's `usr/bin` on PATH for `unzip`. These
  environment fixes changed no tracked scripts.
- **Diagnostics / hygiene:** existing upstream warnings and intentional test
  info are visible in full builds; focused authored targets have no added
  diagnostics. Only local dependency-cache overrides were used, after checking
  exact manifest revisions; package configuration and manifest are untouched.
  Generated Python caches and unselected guarded build artifacts were moved to
  ignored scratch storage. The user's root Markdown inputs and pre-existing
  simulations worktree remain untouched. No upstream publication occurred.
