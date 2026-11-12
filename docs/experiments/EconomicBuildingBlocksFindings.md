# Findings from the economic building-block comparisons

This records the current fork-local results, not a frozen architecture for
economics. The source hypotheses, measurements and commands are in
`EconomicBuildingBlocksLog.md`; the detailed native/guarded comparison is in
`OptimalityFoundationComparison.md`.

## Selected component map

The selection follows `ComponentEvaluation.md`: useful models/theorems and
independent reuse take priority over proof length. Assumptions live on the
operation requiring them. Domain data has its own owner; common mathematics
earns a shared owner through actual consumers.

[The theorem-delivery ledger](EconomicTheoremDelivery.md) tracks subsequent
native applications. Its first path upgrades the existing interior-strategy
report certificate to all original real bids, using explicit payoff coverage
and derived regularity, with the uniform auction as an independent consumer.
The next path packages those incentives as native Bayesian equilibrium under
the actual type law, reusing conditional averaging and bounded-factor
integrability. The uniform consumer computes actual expected utility `13/36`
and bounds all admitted measurable unilateral strategy deviations by it.

| Building block | Concrete reuse and owner | Boundary established |
| --- | --- | --- |
| Explicit rooted comparison and ordered specialization | native `GameTheory/Equilibrium/Problem`; revelation, mixed and Bayesian games | incumbent validity and deviation admissibility have different roles |
| Proof-bearing maps and simulations | native revelation comorphism and measured simulation evidence | exact comparison, domination bounds, retained witnesses and verdicts have different information content |
| Context-dependent witness lifting | `ForMathlib/WitnessLift`; optional native matching adapters, coalition/law/simulation consumers | states and proposals may have different types; composition retains actual intermediate obstructions |
| Potential-difference bounds | `ForMathlib/PotentialBounds`; supporting forms and native Afriat cycles | finite telescoping needs no linear structure on observation indices |
| Supporting linear forms and scalar slopes | `ForMathlib/SupportingForms`, `SupportingSlopes`; IC, monotonicity, optional convexity, payments | pairwise monotonicity loses potential content in multiple dimensions |
| Feasible-point recovery and parametric maximizers | native budget regularity; canonical GameTheory parametric-optimality theorem | closed feasibility alone does not give a closed demand graph |
| Finite law composition and support decomposition | native `FinDist` operations and `FinDist/Support`; pure-deviation and finite-existence theorems | support arguments can work without expected utility; finite scope is explicit |
| Typed action inclusion | existing mechanism/game comaps; actual all-purchase Bayesian control | preserving transfers and prior does not preserve equilibrium when admissible actions change |
| Admissible mixture witnesses | native support plus the optional witness lift; mean and ex-post quantity budgets | a supported improving pure action may be inadmissible; support-heredity is sufficient, not necessary |
| Atomic and nonatomic composition | Mathlib PMF bind support; native probability-measure map/join | infinite discrete support retains positive atoms; nonatomic mixing can lose that provenance while retaining pure witnesses |
| Conditional kernels, averaging and a.e. comparisons | existing native Bayesian machinery plus `InterimAtoms` | null-type beliefs are extra data; arbitrary law preference does not inherit expectation-based recovery |
| Ordinal representation and calibrated aggregation | existing preferences/choice; order reflection and native weighted welfare | pure ordinal choice, expected utility, welfare and monetary units require different invariance assumptions |

The witness operation is optional shared mathematics. It does not make all
domains use one equilibrium, choice, stability or incentive predicate. The
guarded-optimality replacement remains a working comparison branch with genuine
cross-area reuse; its larger footprint is a measured cost, not a proof against
its usefulness.

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
  coordination refutes its converse. Subsequent law-support and simulation uses
  justify a small optional common witness owner, now consumed by native matching
  adapters as well.
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
- **Preferences over laws:** finite support decomposition yields a useful
  pure-deviation theorem without expected utility and retains the contributing
  action. Actual finite stochastic outcome games have full-support possibility
  equilibria. Three lotteries rule out expected-utility representation while
  allowing Boolean scoring. An ex-ante possibility equilibrium can still fail
  conditional optimality at a positive-mass type, so the expected-utility
  information theorem cannot be generalized by replacing its comparison alone.
- **Witness composition:** the optional operation retains an actual intermediate
  obstruction, source context and provenance. Matching reads its original
  membership and singleton block; coalitions keep exact updates; mixed failures
  keep supported actions. Converting a composite simulation preserves a sound
  endpoint bound but can admit witnesses that cannot pass through the specified
  middle stage. The proved relation is strict inclusion, with compatible verdict
  transport. Richer proof data therefore earns a role independently of shorter
  clients; no category or universal equilibrium owner is required.

## What remains informative

All six supplied experiment directions now have compiled evidence, including
the useful law-preference replacement for the original nondiscriminating
criterion. The resumed demand path and the additional supporting-form, blocking,
information, calibration and certificate-conversion paths test interactions
between the components, with both successful consumers and proved boundaries.

Further logical repackaging has diminishing returns on this workload. The next
productive step is theorem delivery using these operations, reopening a
foundation when an actual consumer needs a missing operation or refutes a
stated law. This is evidence for a coherent collection, not a claim that finite
experiments exhaust mathematical economics or identify a uniquely best design.

The outcome-law experiment now supplies named finite theorems and a failed
conditioning generalization. Its original prediction about still needing a
value carrier could not discriminate between designs: the current carrier can
already be an outcome law. No infinite-mixture or general conditional-consistency
theorem follows from the finite results.

The final controls in MEC-015–017 address action restrictions, restricted mixed
menus and discrete/nonatomic provenance. They do not infer infinite-path laws
or conditional consistency of a new preference from static support arguments.
The shared mathematics package boundary remains a separate ownership decision.
No approximate-only existence theorem follows from the exact revelation
example, and no executable algorithm follows from the real-valued law proofs.

Foundational alternatives remain available for local replacement when a new
consumer discriminates between them. Additional theorem families by themselves
are not another architecture experiment.

## Subsequent theorem pressure

The delivery ledger records three distinct obligations that the selected
components keep separate: incentives over original actions, Bayesian equilibrium
under the actual type law, and equilibrium existence across changed auction
parameters. Report IC alone did not supply the first, and a quadratic profit
formula alone did not supply the last.

Repricing is an ordinary domain operation on the mechanism and its auction:
allocation, scarcity and values stay the same, while payments change by the
price difference times own purchases. A function from admissible prices to
these actual auctions, together with pointwise native certificates, expresses
the constructed equilibrium family. No additional family record or equilibrium
predicate is needed. The two-auction profit comparison requests precisely the
common primitives its proof uses, rather than equality of entire models.

This tests composition and change locality beyond logical repackaging. The
uniform consumer still supplies model-specific report IC and the baseline
identity; the existing components supply off-range incentive coverage, guarded
averaging and actual-profit identification. The construction does not turn
those reusable proofs into a general equilibrium-existence theorem, and its
interior regime does not settle other purchase regimes.

The zero-baseline endpoint adds a further consumer of the same coverage and
averaging operations. It is Bayesian Nash with `K=0` and provably lacks the
strict interior certificate. The reusable coverage theorem consequently takes
continuity and a cost-minimizing lowest bid as local premises; the interior
corollary derives those premises from its stronger hypotheses. Regime-specific
derivation certificates remain useful without becoming preconditions on every
equilibrium. At production cost one the endpoint strictly dominates the
constructed interior family, so that distinction has an actual profit consumer.

## Final building-block controls

MEC-015 changes only the original action domain through a typed native comap.
The same included incumbent, prior and transfer rule give opposite actual
Bayesian-equilibrium verdicts. Every payoff is integrable at the prior atom,
so neither filtering nor null-type behavior explains the difference. The
restricted consumer uses the general mechanism/game API; the entire real-bid
auction analysis is not automatically transferred to a new carrier.

MEC-016 refutes pure sufficiency under a genuine mean-quantity budget, with a
valid incumbent and nonempty admitted pure menu. A guarded witness lift repairs
transport when the extracted pure obstruction remains admitted. Support-heredity
is one sufficient construction. A deliberately stronger ex-post budget supplies
a native positive consumer with the same raw-law evaluation. The missing
finite-mixture right-unit identity now lives with native finite support facts.

MEC-017 supplies the countable evidence separately: a geometric PMF has proved
infinite support, and native law-valued response equilibrium uses Mathlib bind
support against every PMF deviation. The nonatomic control uses actual native
mixing and flattening: success is certain and every pure continuation succeeds,
but every action singleton has zero mass. Thus existence of a witness,
positive atomic provenance and topological support must remain distinct.

The [closure record](BuildingBlockClosure.md) classifies the remaining scope.
The identified competitions have no further discriminating native consumer on
this workload. Further theorem delivery alone does not justify another
foundation experiment. Preserve the inconclusive certificate-compression
prediction, nondiscriminating original law-carrier criterion and working rival
foundations rather than reporting every historical hypothesis as confirmed.

## Verification

At the original component gate, complete and explicit builds cover 283
authored modules (9,333 jobs). The project-wide kernel audit checks 6,224
declarations with only standard axioms. The source-token scan covers every
authored file with zero violations. Changed sources were re-elaborated at each
slice, including all nine current files in the final slice, with zero violations;
unchanged sources were not all re-elaborated by the source audit at the final gate.

New files pass strict warning/line-length checks. Header and generated-import
checks and native BIC exact-arithmetic checks pass. The unchanged audit/helper
harnesses passed 21 integrity, 28 warning-report and 11 import-helper tests at
the earlier gate. Existing upstream warnings remain visible. The separate shared-
demand branch also passed its full build and 267-module kernel gate before its
separately checked final boundary control. The ledger records exact scope.

The final MEC-015–017 closure gate includes the intervening theorem deliveries:
complete and explicit builds pass 9,354 jobs across 304 authored modules.
The kernel audit checks 6,478 declarations with only standard axioms. The
all-source token scan has zero violations. All six Lean files changed in the
final three experiments re-elaborate with zero violations and no discarded
declarations, and pass strict warning/line-length checks using generated Lake
module setups. Header, generated-import and native BIC checks pass. Dependency
pins and toolchain remain unchanged. The identified experiment queue is closed;
no uniquely best foundation or completeness across the field is asserted.
