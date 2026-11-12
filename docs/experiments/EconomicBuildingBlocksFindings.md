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
complete build and integrity checks. It was not selected for collection because
its measured proof/repair cost exceeded the simplified native baseline. Its
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
4. **A common normal form does not automatically earn proof ownership.**
   Guarded coverage really serves game transport and choice contraction without
   extra assumptions. Nevertheless the replacement adds 121 nonblank code lines
   across 18 files, and both representative proofs become longer. These menus
   already enforce most of the reconstructed guards. This is a negative result
   for forcing this representation into these owners, not a ban on shared math.
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

## What remains informative

Further variations of the same logical packaging now have diminishing returns.
The next useful test is a different economic dependency path: demand with changing
price/wealth budgets, including zero wealth under positive prices, or a named
auction equilibrium theorem that needs the proposed mathematical operation.
The earlier demand probe is deferred before compilation, not refuted.

The proposed outcome-law experiment has not been run. Its original prediction
about still needing a value carrier cannot discriminate between designs: the
current carrier can already be an outcome law. A useful successor must name a
law-preference theorem and an actual failed transport or mixture-closure step.
No general existence or infinite-mixture theorem follows from the present work.

These limits keep the general field-level conclusions provisional while making
the next experiment concrete. Foundational alternatives remain available for
local replacement whenever a new consumer can discriminate between them.

## Verification

The selected implementation passes the complete build and an explicit build of
all 255 authored modules (9,305 jobs). The project-wide compiled audit checks
5,870 declarations with only standard axioms; the source-token scan finds no
holes. Individual experiment gates cover source elaboration, including
discarded examples. Header/import checks and the 21 integrity, 28 warning-report
and 11 import-helper harness tests pass. Existing upstream warnings remain
visible. The ledger records commands, environment adjustments and precise scope.
