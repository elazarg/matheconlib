# Optimality foundations: native specialization and guarded coverage

Evidence: MEC-004 and MEC-005 in `EconomicBuildingBlocksLog.md`.

The collecting branch selects the native canonicalization. The complete guarded
replacement remains on `codex/experiment-economic-item-05b-guarded-core` as a
working alternative. This selects an implementation for the measured slices;
it does not freeze the underlying design choices.

## Independent native control

`IsDeviationOptimal` and `IsEquilibrium` transparently specialize their explicit
comparison forms. Ordered morphism/comorphism transports reuse the corresponding
comparison theorem. Incumbent validity remains a separate outer field.

This removes duplicate ownership without introducing another predicate. There
are two internal namespace repairs and no downstream proof repairs. The ordinary
revelation client using a factored direct theorem becomes one application, just
like the record client. The original conversion overhead was therefore evidence
about duplicate representation, not an intrinsic advantage of records.

## Actual guarded replacement

The rival changes the native `IsOptimalWith` definition to `IsOptimalOn True`
over the admitted-deviation menu. Ordered and explicit judgments share this
owner. Both native map transports use the same coverage theorem as the attained
bundle-choice contraction proof. A preference-maximizer bridge and Mathlib
`IsMaxOn` bridges account for their different feasibility requirements.

No comparison laws or additional economic hypotheses enter these statements.
Candidate validity stays outside the player quantifier, including when there
are no players. Target validity is not required. Existing mixed/Bayesian
integrability filters remain in the deviation menu. Thus the rival is a real
foundational replacement with equivalent semantics, not just a wrapper demo.

Counts below exclude block comments and blank lines. Proof-body counts exclude
the opening `by`. They correct the initial rough count of the choice proof:
its native body has five lines under this convention, not six.

| Item | Native canonicalization | Guarded replacement |
| --- | ---: | ---: |
| Explicit morphism transport body | 3 | 7 |
| Explicit comorphism pullback body | 3 | 7 |
| Attained choice contraction body | 5 | 9 |
| Core module, whole code | 281 | 302 |

The entire replacement adds 121 nonblank code lines across 18 files:
59 in the Mathlib-only operation and bridges, 21 in the core, five in choice
contraction, four in the preference-maximizer bridge, 31 in consumer repairs,
and one umbrella import. The repairs include eight test files, four strategic
modules and one example file; some replace a line without increasing its count.
There is no performance claim from these counts or cached build timings.

The guarded variant passes complete `lake build` (9,303 jobs). Its new leaf and
core pass focused warning-as-error builds. Unrelated warnings already present
in upstream remain visible. Integrity reports are recorded in the experiment
ledger when complete.

## What this supports

Guarded coverage is expressible without game imports and really is reused in
two areas, with unchanged hypotheses. That part of the operations hypothesis
survives. Requiring it to own these native definitions does not earn a reduction
in proof work: these consumers mostly reconstruct or discard guards that their
existing menus already enforce. The smaller native control is the better
implementation on this workload.

This does not refute a mathematical operation with another demonstrated
consumer, nor establish a universal equilibrium record. The revelation map
earns reuse within the strategic layer; its cold construction is still charged.
Choice retains its attained-feasibility meaning. A later foundational change
can be tested just as freely against these retained alternatives.
