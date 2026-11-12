# Economic building-block experiment log

This log belongs to the fork-local investigation described in
`EconomicBuildingBlocks.md`. Item identifiers here are independent of the
earlier GameTheory experiment ledger.

Evaluation now follows `ComponentEvaluation.md`: useful expressiveness, actual
reuse and composition take priority over proof length. Earlier measurements
remain evidence, but line-count increases alone do not reject a component.

## MEC-007: supporting slopes as a reusable incentive interface

- **Date / status:** 2026-11-12; complete, including the MEC-009 batch gate.
- **Question:** Can an action-free supporting-slope condition own incentive
  mathematics for both native single-good problems and multi-unit quantities,
  while preserving the distinction between report and universal deviations?
- **Alternatives:** native action/strategy-based IC and its existing reduced
  form; a mathematical condition on a type set and functions `U` and `q`.
- **Representative slice:** prove exact native envelope/type-deviation
  equivalence, derive native monotonicity and utility convexity from the same
  operation, and validate an unbounded-quantity truthful model excluded by the
  native allocation range. Retain a profitable unused-action control showing
  that reduced IC does not imply universal IC.
- **Kill conditions:** no hidden allocation bound, interval nonemptiness,
  continuity or surjectivity in the supporting condition. Use existing native
  analytic/payment results where applicable. Useful additional models and
  downstream reuse outweigh a longer proof; do not call a missing hypothesis
  an API improvement.
- **Artifacts / baseline:** collecting `d6b4268`; child
  `codex/experiment-economic-item-07-reduced-incentives`. Search Mathlib before
  introducing a supporting-slope predicate; public ownership remains open
  until consumers compile.
- **Result:** `ForMathlib/SupportingSlopes.lean` and its optional `Convexity`
  module prove monotonicity, convexity and canonical report-payoff bounds with
  no quantity bound, continuity, action carrier or interval assumptions.
  Native `HasEnvelopeIC` now transparently wraps this mathematical condition;
  native `q_monotoneOn` reuses it. `SingleParameter/ConvexUtility.lean` adds
  convex indirect utility. The reverse envelope/report IC implication is
  proved explicitly; only the original instance direction is installed, so
  typeclass search has no implication cycle.
- **Useful expressiveness / reuse:** the same operation validates truthful
  quadratic payments for `q(v)=2v`, with quantities unbounded on nonnegative
  types. This rule cannot be represented by the native globally unit-bounded
  quantity function. This does not prohibit representation on a restricted
  small interval and does not fault the native single-object scope. The
  supporting condition also feeds the unchanged native analytic payment
  identity. An unused subsidy action gives reduced universal/report IC while
  refuting original universal IC, preserving the representation boundary.
- **Validation / selection:** `lake --iofail build` on the native payment,
  convexity and consumer targets passes 2,732 jobs without diagnostics.
  Compiled integrity checks cover 82 declarations across seven modules with
  standard axioms only. Retain the component for its broader truthful model
  and actual mathematical reuse, rather than for a line-count reduction.
  Umbrellas are regenerated; whole-project integration is a later batch gate.

## MEC-008: blocking witnesses and typed proposal reductions

- **Date / status:** 2026-11-12; complete, including the MEC-009 batch gate.
- **Question:** Which reusable operation belongs beneath coalition/contract
  stability when proposals differ from states? Does preserving positive
  blocking witnesses earn more reuse than merely packaging stable predicates?
- **Alternatives:** native witness theorems and direct composition; an optional
  state/proposal blocking interface with witness-lifting reductions. No reward
  carrier or artificial order encoding is required in either route.
- **Representative slice:** extract the stronger theorem that every member of
  a blocking contract set supplies a singleton block under substitutability;
  reuse it in native stability and in extracting an actual marriage blocking
  pair belonging to the original contract proposal. Compose typed witness
  reductions and preserve individual rationality separately.
- **Kill conditions:** preserve nonempty/new-contract requirements and explicit
  marriage IR. Do not add finiteness, IRC or a global order. A complementary
  contract market must block jointly without any blocking singleton, refuting
  an unconditional witness reduction. Consent is not inferred from all changed
  outcome coordinates. Strong-Nash strict-gain bridges retain comparability.
- **Baseline / branch:** the selected MEC-007 implementation; planned child
  `codex/experiment-economic-item-08-blocking-witnesses`. Public ownership of a
  new interface is conditional on actual witness reuse, not expressibility.
- **Useful result:** native `Market.Blocks.singleton_of_mem` extracts a
  singleton block for every member of a blocking set under substitutes.
  `Blocks.exists_singleton` retains membership in the original proposal and
  replaces the inline native pairwise-to-stable proof. The marriage bridge
  `exists_blockingPair_mem_of_blocks_graphOf` composes it with the existing
  dictionary, retaining incumbent IR and proposal membership without finite
  agent or finite proposal assumptions.
- **Optional component:** test-only `WitnessLift` separates states from
  proposals and retains a state-dependent relation between blocking witnesses.
  `covers`, `comp` and `transport` are used by contract singleton reduction,
  marriage witness extraction and unilateral-to-collective gain lifting.
  Native IR is transported separately; the matching candidate subtype retains
  the necessary IR certificate. No reward carrier or artificial order appears.
- **Expressiveness finding:** matching membership initially worked with an
  unrooted witness relation. Exact coalition updates require the incumbent in
  that relation. `no_unrooted_exact_update` refutes exact update characterization
  by a state-independent relation for the fixed proposal/profile types. The
  interface was broadened accordingly. This does not rule out richer proposal
  encodings or weaker unrooted provenance.
- **Negative controls:** an actual complementary contract market is pairwise
  stable but jointly blocked and fails substitutes. A coordination game has
  no unilateral strict gain but has a collective gain. Thus witness lifting
  is correctly unilateral-gain to collective-gain, yielding no-collective to
  no-unilateral absence transport; it does not assert the converse. The native
  strong-Nash/strict-blocking iff retains precisely local comparability.
- **Validation / selection:** contract core, complementarity and coalition
  targets pass strict builds. Marriage and witness consumers pass normal Lake
  builds and independent warning-as-error source checks; their target builds
  replay only the pre-existing `Choice.Induced` reducibility warning. Semantic
  review passes. Retain strengthened native witness APIs and the optional
  prototype for further reuse/coherence tests. Full integration remains a
  batch gate; no universal blocking record or category instance is adopted.
- **Integrity:** compiled checks cover 167 declarations across both native
  modules and all four prototype/control modules, using only standard axioms.
  The optional interface is evidence for reusable positive witness transport;
  direct existential composition remains an equally admissible implementation.

## MEC-001: native demand regularity and a shared maximizer operation

- **Date / status:** 2026-11-12; initially deferred before compilation;
  resumed under MEC-009 with the original hypothesis and controls retained.
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

## MEC-009: parametric demand and actual cross-library theorem reuse

- **Date / status:** 2026-11-12; complete, native and shared dependency branches validated.
- **Question:** Does the existing general closed-feasible-maximizer operation
  provide useful native demand regularity without prescribing choices, positive
  wealth, compactness or a permanent library dependency?
- **Alternatives:** use the canonical compiled GameTheory mathematical module
  through a transient local path dependency; compare with a new shared owner
  only after this cross-library consumer compiles. Do not copy its proof into
  a second authored owner merely to make reuse appear successful.
- **Representative slice:** native nonnegative commodity budgets, continuous
  strictly positive prices and continuous nonnegative wealth including zero.
  Prove lower hemicontinuity and closed feasible graph, then closed graph of
  native utilityChoice for continuous utility, retaining all ties. Link observed
  Dataset budgets by an explicit native-semantic identity.
- **Kill conditions:** no choice selection, positive-wealth assumption or
  compactness/existence conclusion slipped into the graph theorem. Refute lower
  hemicontinuity at zero price and zero wealth. Keep dependency and shared-owner
  decisions separate from the mathematical component's usefulness. Preserve
  the sibling checkout and its unrelated user changes.
- **Artifacts / baseline:** collecting 7070d21; child
  codex/experiment-economic-item-09-parametric-demand. Any temporary Lake
  dependency update must be generated by Lake and measured, never hand-edited
  in the manifest. It need not become a permanent collected dependency.
- **Native feasibility gate:** `linearBudgetSet` is the common price/wealth
  feasible set in `RevealedPreference.Basic`; native `Affordable` specializes
  it and `budgetSet_eq_linearBudgetSet` identifies observed budgets exactly.
  The rebase needs one explicit goal-shape adjustment in an existing proof.
  `BudgetRegularity` proves lower hemicontinuity at strictly positive prices
  with continuous nonnegative wealth, including zero wealth, plus closedness
  of the feasible graph without price positivity. These targets and controls
  pass strict builds (2,085 jobs).
- **Hostile controls:** a continuously vanishing squared price and zero wealth
  give a closed budget graph but fail lower hemicontinuity at the free-good
  boundary. Continuous linear utility on a two-good unit budget chooses both
  distinct corners. No selected demand, uniqueness or general existence
  theorem is substituted for the native maximizing correspondence.
- **Native integrity:** compiled checks cover 83 declarations across the four
  changed native/control modules, with only the standard axioms. The native
  feasibility changes do not depend on GameTheory; cross-library theorem reuse
  is the next separately reviewable branch.
- **Shared theorem gate:** the sibling GameTheory path dependency and its
  existing fixed-point-package path override are generated by `lake update`;
  all nine shared third-party revisions and the Lean 4.35 toolchain match.
  `ParametricDemandConsumer.isClosed_demandGraph` compiles against the canonical
  `GameTheory.Math.ParametricOptimality` module, without copying its proof.
  Utility can vary jointly with the parameters; wealth may be zero and all
  native demand ties remain. Strict focused build passes and the six-module
  axiom audit covers 91 declarations with standard axioms only.
  The canonical source is clean at GameTheory head `9f74339e`, last changed in
  `ec2977ff`; SHA256 `4127f15400525f3a438299c774e562a918facfa868a9851d3270e0b4b21fa631`.
  Dependency integration is checked on child
  `codex/experiment-economic-item-09b-shared-demand-theorem`; no permanent
  dependency or second mathematical owner is implied.
- **Stronger graph control:** `DemandGraphBoundary` has continuous peaked
  utility, a closed feasible graph, and nonempty native demand at every
  parameter, yet its demand graph is not closed. At zero price one unit is
  optimal; away from it only zero is affordable. Nonattainment is therefore
  not the reason the graph theorem fails without recovery. Its strict target
  and source elaboration pass; the seven-module focused audit covers 104
  declarations with standard axioms only.
- **Integrated shared branch:** full build passes 9,319 jobs. Before the last
  additional graph control, explicit project coverage checked all 266 native
  modules plus the canonical shared module: 5,988 declarations, standard
  axioms only, zero source-token violations. All 19 changed source files since
  the first collection were re-elaborated with zero violations; the additional
  control was checked separately. This closes the batch gate for MEC-007/008
  and proves actual package-level reuse for MEC-009. The path dependency is
  retained on its evidence branch; collection retains native geometry without
  making this a permanent package boundary.
- **Collected native configuration:** restored the original Lake configuration
  and nine-package manifest by returning to the native parent branch. The
  independent budget geometry and both native control files pass a complete
  build without the temporary GameTheory dependency (9,316 jobs). The shared
  demand theorem remains reproducible on `a137839` and its named evidence
  branch. A shared mathematical owner can be chosen separately from proving
  reuse; this experiment does not create a duplicate owner.

## MEC-010: multidimensional supporting forms and finite cycles

- **Date / status:** 2026-11-12; complete, collected with full build and source checks.
- **Question:** Does the successful scalar supporting-slope interface extend
  to genuinely multidimensional IC without an inner product, topology, slope
  bounds or chosen action representation? Which content is lost by replacing
  it with pairwise monotonicity?
- **Alternatives:** scalar support as a special case of supporting linear
  forms on a real module; independently duplicated multidimensional IC proofs;
  pairwise monotonicity without a potential.
- **Representative slice:** reuse a general supporting-form theorem for scalar
  utility convexity and a two-dimensional truthful mechanism. Derive finite
  cyclic inequalities by summing supports, and refute potential representation
  for the rotation field despite its pairwise monotonicity.
- **Kill conditions:** exact scalar specialization, no unnecessary topology
  or finite-dimensional hypothesis in the shared theorem, actual truthful
  payment consumer and an explicit violating cycle. A stronger component wins
  through useful theorems and reuse, even if its interface/proofs are longer.
- **Artifacts / baseline:** the collected scalar component from MEC-007;
  prototypes remain ignored until the current build finishes. No category or
  convex-analysis hierarchy is introduced merely to package this condition.
- **Design observation:** the direct scalar specialization through opaque
  Mathlib `LinearMap.mulRight` compiles as mathematics but obscures scalar
  arithmetic from existing IC automation. An independent native consumer
  suggests a useful lower operation: Afriat inequalities bound utility
  differences by indexed expenditure increments without any linear structure
  on observation indices. Test common potential-difference bounds beneath both
  supporting forms and scalar slopes, reusing the same finite-cycle theorem
  for a native Afriat expenditure-cycle result. Retain the failed direct
  normalization observation; the extra layer needs this independent reuse,
  not merely a shorter scalar proof.
- **Focused result:** `PotentialBoundsOn` owns finite-permutation telescoping
  without algebraic assumptions on points. Supporting forms and scalar slopes
  transparently specialize it; scalar wrappers reuse the linear-form payment,
  monotone-pairing and convexity theorems through explicitly supplied linear
  maps. Keeping scalar increments visible restores native IC automation without
  changing its proofs. Native `AfriatInequalities.potentialBounds` and
  `sum_cycle_nonneg` reuse the same telescoping proof on observation indices,
  without positive multipliers or finite observation sets.
- **Hostile controls:** quadratic utility on `ℝ × ℝ` has truthful canonical
  payments. The rotation field has zero pairwise pairing everywhere but positive
  sum on a three-point cycle, so it has no supporting potential. This refutes
  replacing support by pairwise monotonicity in multiple dimensions.
- **Commands:** the strict focused build of ReducedIncentiveConsumer,
  SupportingFormsConsumer, SingleParameter.ConvexUtility and AfriatCycles passes
  (2,743 jobs). Full build passes 9,321 jobs. The seven-module kernel audit
  checks 43 declarations with standard axioms only; source elaboration checks
  all nine changed Lean files with zero violations and no discarded examples.
  Semantic review confirms orientations and scope; a coordinate-square docstring
  was clarified to avoid confusing the product norm with the Euclidean norm.
  **Outcome:** select the small potential/support operations and native Afriat
  consumer; no convex-analysis hierarchy or universal optimization hub is needed.

## MEC-011: conditional information, averaging and null signals

- **Date / status:** 2026-11-12; complete, including full build and source checks.
- **Question:** Which existing information/averaging components already serve
  interim and ex-ante incentives, and what is lost at null signals? Can a
  mere judge-index map represent the relevant aggregation?
- **Alternatives:** existing conditional kernels, almost-everywhere judgments,
  finite weighted comparisons and nonzero-atom localization; a new information
  record or an unjustified global pointwise equivalence.
- **Representative slice:** reuse native ex-ante/interim theorems under a
  correlated finite prior with positive marginal types but missing joint atoms.
  Extend the existing two legitimate conditional-belief versions of a null
  prior to an actual mechanism: ex-ante BNE is fixed while pointwise BIC changes
  on a null type. Expose an atom-localized API only if it is not already present.
- **Kill conditions:** no independence or full joint support added for
  convenience, no claim of pointwise incentives at null types, no integrability
  loophole, no recreation of existing averaging or disintegration theorems.
  Distinguish a simultaneous conull condition from separate per-action nullsets.
- **Baseline:** current native conditional-belief and Bayesian APIs. Read-only
  inspection finds the positive-marginal finite equivalence and a.e. measurable
  theorem already implemented; they are the comparison baseline, not new work.
- **Focused result:** native `Measurable/InterimAtoms` adds nonzero-singleton
  localization of a common conull incentive comparison, using Mathlib's a.e.
  filter. Its BNE corollary keeps the existing measurable-payoff and simultaneous
  conditional-integrability guards. It adds neither independence nor finite or
  countable type/action assumptions.
- **Actual consumers:** `ConditionalIncentiveControls` keeps the same mechanism,
  full true-type-dependent values, transfers and prior across two valid belief
  versions. Native BIC averaging gives truthful ex-ante BNE under one version;
  pointwise BIC fails under the other at the zero-mass type. All comparisons are
  integrable. `ConditionalIncentiveCorrelated` uses the same mechanism under a
  correlated prior: every marginal singleton has mass one half, a mixed joint
  profile is null, and native averaging plus atomic recovery proves truthful
  BIC/BNE and all pointwise interim comparisons.
- **Command:** `lake --iofail build
  MathEconLibTest.GameTheory.ConditionalIncentiveCorrelated` passes (3,118 jobs),
  including the null-type consumer. Existing conditional kernels and averaging
  already provide the substantive operations. A judge-index map alone supplies
  neither integration nor the common conull comparison; an extra information
  record has not earned a role. Full build passes 9,324 jobs; the three-module
  kernel audit checks 38 declarations with standard axioms only. All five changed
  Lean sources re-elaborate with zero violations and no discarded examples.

## MEC-012: private utility recodings and common welfare calibration

- **Date / status:** 2026-11-12; complete, including full build and source checks.
- **Question:** Which mathematical operation separates private ordinal choice
  from the common calibration used by native efficiency and monetary statements?
- **Alternatives:** ordinary finite weighted sums and existing `IsMaxOn`
  invariance; a new scale/utility hierarchy. Use the former unless a real
  consumer requires additional structure.
- **Representative slice:** add weighted total value beside native totalValue,
  prove covariance under agent-specific affine recodings with reciprocal
  weights, and consume it in native `IsEfficient`. Preserve all private choice
  menus under recoding while reversing unweighted efficiency. Restore the
  original objective by explicit weights.
- **Kill conditions:** covariance algebra needs nonzero factors; economically
  order-preserving recodings need positive ones. Shifts may depend on type but
  not on the compared outcome. Scaling valuations while holding transfers fixed
  is not a harmless recoding of quasilinear utility. Test that failure, full
  utility recoding, and budget balance under common versus private factors.
  Do not claim observed choices identify utility up to affine maps; ordinal
  invariance is broader.
- **Ownership baseline:** native `QuasilinearEnvironment.totalValue`, native
  `DirectMechanism.IsEfficient`, existing `Choice.maximizers` and Mathlib
  `IsMaxOn`/finite-sum algebra. No new scalarization owner is presumed.
- **Focused result:** `Core/WeightedWelfare` adds explicit weighted total value,
  the reciprocal-weight affine covariance identity and a native `IsEfficient`
  equivalence. The shared all-menu theorem lives in existing `Choice.Maximizers`
  and uses Mathlib order reflection. It serves independent welfare and lottery
  consumers without requiring a scale class.
- **Controls:** two agents' outcome choices agree on every menu under positive
  private factors, while native total-value efficiency reverses. Reciprocal
  weights restore it. Scaling valuation alone reverses buy/decline with fixed
  money; scaling the complete utility or both valuation and transfers preserves
  the displayed comparison. Common transfer factors preserve budget balance;
  private factors can destroy it. No participation or fixed-zero outside-option
  invariance is claimed.
- **Expectation boundary:** `ExpectedRecodingBoundary` has identical choices on
  every pure-outcome menu for utilities `(0,1,3)` and `(0,1,3/2)`, but opposite
  native expected-value comparisons of the half-first/half-third lottery with
  the sure middle outcome. It proves the utilities are not positive-affine
  recodings. Primitive ordinal utility changes therefore cannot be pushed
  through expectation using the all-menu score theorem.
- **Commands / review:** the focused build of WeightedWelfareConsumer and
  ExpectedRecodingBoundary passes (3,065 jobs), with existing upstream simplex
  deprecations visible. Both consumer files pass `lake env lean
  -DwarningAsError=true -Dlinter.style.longLine=true`; semantic review confirms
  covariance, assumptions and the monetary/ordinal distinctions. Full build
  passes 9,327 jobs; the four-module kernel audit checks 91 declarations with
  standard axioms only. All six changed Lean files re-elaborate with zero
  violations and no discarded examples. **Outcome:** explicit weights and
  ordinary order reflection suffice; a scale hierarchy adds no needed operation.

## MEC-013: possibility preferences over outcome laws

- **Date / status:** 2026-11-12; reserved, independent draft preparation.
- **Question:** Can support-based preferences deliver a useful equilibrium
  theorem without expected utility, while retaining the actual probability law?
- **Alternatives:** native law and support operations plus explicit comparisons;
  a universal preference-over-laws class; expected-value scalarization.
- **Representative slice:** derive pure-deviation sufficiency from the support
  of an admitted mixed deviation, retaining its contributing pure action. Test
  a full-support equilibrium and a preference not representable by expected
  utility. Reuse the witness operation if it preserves the needed provenance.
- **Kill conditions:** an actual theorem about native probability operations,
  not universal encodability. No silent substitution of expected-payoff Nash,
  no infinite-mixture conclusion from a finite-mixture proof, no copied law
  carrier and no unproved mixture-closure premise.
- **Cross-control reserved before implementation:** test whether the expected-
  utility atomic recovery from MEC-011 could extend to arbitrary law comparisons.
  Under a fair binary prior, success at the first type already saturates ex-ante
  possibility. The second, positive-mass type may still admit a conditional
  improvement. Use native finite laws and all mixed contingent deviations;
  do not misstate the existing expectation-based theorem as refuted.

## MEC-014: certificate conversion and retained provenance

- **Date / status:** 2026-11-12; reserved, independent draft preparation.
- **Question:** Does converting a composite simulation preserve the same witness
  relation as composing the converted obstruction lifts?
- **Alternatives:** equality of retained provenance; one-way inclusion with
  equivalent verdict transport; discarding witnesses and comparing only verdicts.
- **Representative slice:** convert simulations to lifts of admissible bad
  deviations, including incomparable violations. Prove the sound composition
  direction and test strictness using a middle stage whose only improving
  deviation has value two, between target value one and source alternatives
  of values one and two.
- **Kill conditions:** preserve judge maps, admissibility, source context and
  bound direction. Do not claim equality from verdict equivalence or install
  category structure merely to package composition.
- **Optional ownership comparison:** after the four independent matching,
  coalition, law-support and simulation consumers compile, test a probability-
  free public witness operation and optional native matching adapters. The old
  prototype's composed relation remembers an intermediate relation witness but
  does not itself include the middle-obstruction proof. Compare an explicit
  guarded composition that retains that proof; advertise exactly its stronger
  provenance contract. Keep the original prototype on its evidence commits,
  and do not replace native verdict predicates or impose a hierarchy.
