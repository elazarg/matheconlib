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
