# Findings from the economic building-block comparisons

This records the current fork-local results, not a frozen architecture for
economics. The source hypotheses, measurements and commands are in
`EconomicBuildingBlocksLog.md`; the detailed native/guarded comparison is in
`OptimalityFoundationComparison.md`.

## What actually changed

The experiment fast-forwarded the local fork and `origin/main` to upstream
`b0c6f35`, then worked on named child branches collected by
`codex/experiment-economic-building-blocks`. No worktree was created.
User-supplied design documents were preserved as committed snapshots.

The selected core changes are substantive: strong Nash now has a theorem under
local comparability rather than a global linear order, and ordered optimality
and equilibrium transparently specialize their explicit-comparison definitions.
The former is tested with vector rewards and an incomparability counterexample;
the latter is tested through the existing library and an empty-player validity
control.

A competing branch actually replaced native per-player optimality with a
Mathlib-only guarded predicate, rerouted map proofs through coverage, and changed
a native choice contraction proof to use that same operation. It passed the
complete build and integrity checks. The initial selection favored the simpler
native implementation. Under the revised expressiveness-first criteria, the
larger footprint does not refute guarded coverage: it establishes real shared
mathematics, but has not yet shown a benefit from making every native judgment
use that representation. Its
working source remains on `codex/experiment-economic-item-05b-guarded-core`.
The alternatives were changed and compared locally; existing design choices
were not treated as constraints on the experiment.

## What the comparisons say

1. **Maps earn reuse inside the strategic layer.** The same revelation
   comorphism transports exact BNE and arbitrary explicit comparisons. The
   generic theorem preserves true types, full transfers, the prior and the
   integrability filter, without requiring surjective strategies. The concrete
   second error bound follows from exact BNE, so it is not an independent
   approximate-equilibrium existence example.
2. **Ordinary functions and theorems also compose.** Factoring the direct
   revelation theorem removes duplicated proof work. Canonicalizing ordered
   equilibrium removes its conversion overhead. Chained reductions can compose
   direct equivalences with `Iff.trans` through any finite number of stages.
   A short record client alone is not evidence that this reuse is unavailable
   without records.
3. **Certificate output is richer than a verdict.** Simulation composition
   retains value maps, deviation witnesses and validity proofs. Direct verdict
   induction needs none of that output. Both are useful deliverables; their
   costs must be compared at the same requested strength. Global packaging also
   asks more than a theorem about one incumbent.
4. **A common normal form needs a useful shared operation.**
   Guarded coverage really serves game transport and choice contraction without
   extra assumptions. The replacement adds 121 nonblank code lines across 18
   files, and both representative proofs become longer. That is a cost, not a
   decisive objection. These menus already enforce most reconstructed guards;
   the open question is which additional theorem or model benefits from common
   ownership. Independent ownership remains available without replacing every
   native predicate.
5. **Evaluation conventions are mathematical content.** The positive
   infinite-gain fixture is a native mixed equilibrium against every admitted
   integrable deviation. Its accepting deviation has nonnegative integral top
   and is excluded. An explicit law-valued comparison admits that move and
   rejects the same valid incumbent. That change is expressible in the current
   carrier, but it changes semantics. Repackaging guards has not demonstrated
   a cheaper equivalent certificate.
6. **Assumptions belong at their actual use.** Strong Nash needs comparability
   only on the compared pairs. Invalid deviation targets can defeat equilibrium;
   invalid incumbents remain rejected even with no judges. A column may become
   dominated only after an opponent restriction. These are enforced controls,
   not prose conventions about where definitions live.

The resulting direction is a combination of domain-owned semantics,
transparent specializations, and reusable operations or certificates whose
actual consumers justify their cost. These comparisons do not establish a
universal equilibrium hub or reduce matching, choice and mechanism design to
one predicate. Nor do they show that equilibrium records are merely vocabulary:
the revelation and simulation workloads reuse their proof-bearing maps.
Encoding a concept through an arbitrary value carrier and comparison is not,
by itself, evidence that this representation should own its downstream proofs.

## Expressiveness-first follow-up

The evaluation criteria are explicit in `ComponentEvaluation.md`: semantic
adequacy, useful expressiveness, actual reuse, composition and change locality,
interface quality, then cost. A short proof is evidence about cost; a new model
or reusable theorem is evidence about capability. Neither counts declarations
or hypothetical encodings as successful reuse.

- **Reduced incentives:** scalar supporting slopes now serve native envelope
  IC, allocation monotonicity, utility convexity and payment theory. A multi-unit
  example exceeds the native globally unit-bounded allocation model. A mechanism
  with an unused subsidized action proves that truthful-report IC cannot replace
  universal original-action IC.
- **Obstruction witnesses:** substitutable contract choice decomposes every
  joint block into singleton witnesses. The native marriage bridge returns an
  actual blocking pair from the original block. A complementary market refutes
  singleton sufficiency without substitutes. Coalition transport reuses a
  context-dependent witness operation, retaining exact update provenance;
  coordination refutes its converse. The generic operation remains a prototype
  until further independent uses justify its public ownership.
- **Changing choice sets:** native positive-price budgets admit feasible-point
  recovery even at zero wealth. The demand graph theorem compiles against the
  actual canonical GameTheory parametric-optimality theorem on a separate shared
  dependency branch, without copying its proof. Closed feasible graphs and
  nonempty demand alone fail in a free-good boundary control. Collection keeps
  independent budget geometry; the shared theorem branch is evidence for a
  common mathematical owner, without prematurely selecting a package boundary.
- **Dimensions and potentials:** scalar support extends to linear forms on a
  real module without topology or an inner product. Potential-difference bounds
  share one finite-cycle proof between those incentives and native Afriat
  inequalities on observation indices. A rotational field passes all pairwise
  monotonicity comparisons but violates a three-point cycle, proving that the
  stronger potential content is necessary. Direct scalar normalization through
  opaque linear maps hurt arithmetic automation; the lower operation keeps
  scalar increments transparent while preserving shared mathematical proofs.
- **Conditional information:** the native kernels and averaging theorems already
  carry the required structure. A small atom-localization theorem recovers the
  common conull comparison at every type with nonzero marginal singleton mass.
  An actual mechanism has the same prior and ex-ante equilibrium under two valid
  belief versions, but different pointwise BIC at a null type. A correlated
  positive-marginal consumer works despite missing joint atoms. This supports
  kernels, integration and a.e. judgments as separate operations; mere judge
  reindexing cannot perform their aggregation.
- **Utility and welfare calibration:** ordinary strict-monotone order reflection
  preserves all pure menus and ties. Explicit reciprocal welfare weights preserve
  native efficiency under independent affine value recodings. Unweighted welfare
  can reverse despite identical individual outcome choices. Fixed monetary units
  and expected-lottery preferences require more structure: valuation-only scaling
  can reverse buying, and two ordinally equivalent utilities give opposite expected
  lottery comparisons. Common transfer factors preserve balance; private factors
  can destroy it. A scale hierarchy was unnecessary for these consumers.

## What remains informative

Further variations of the same logical packaging have diminishing returns.
The changing-budget path has now been tested. Conditional information, welfare
calibration, law preferences and certificate-conversion provenance are the next
discriminating paths; their reserved experiments preserve explicit kill
conditions. A new abstraction must improve those consumers rather than merely
rename a condition.

The proposed outcome-law experiment is in draft preparation. Its original prediction
about still needing a value carrier cannot discriminate between designs: the
current carrier can already be an outcome law. A useful successor must name a
law-preference theorem and an actual failed transport or mixture-closure step.
No general existence or infinite-mixture theorem follows from the present work.

These limits keep the general field-level conclusions provisional while making
the next experiment concrete. Foundational alternatives remain available for
local replacement whenever a new consumer can discriminate between them.

## Verification

The first collection passes the complete build and an explicit build of
all 255 authored modules (9,305 jobs). The project-wide compiled audit checks
5,870 declarations with only standard axioms; the source-token scan finds no
holes. Individual experiment gates cover source elaboration, including
discarded examples. Header/import checks and the 21 integrity, 28 warning-report
and 11 import-helper harness tests pass. Existing upstream warnings remain
visible. The later reduced-incentive, obstruction and budget collection also
passes full builds; the shared-demand branch covers 267 modules and 5,988
declarations before its separately checked final boundary control. Newer focused
gates and pending integration checks are recorded in the ledger; do not read the
earlier counts as coverage of later unbuilt drafts.
