# Evaluating mathematical building blocks

The user's instruction on 2026-11-12 gives useful expressiveness and reuse
priority over proof length. All basic abstractions remain replaceable locally.

## Established guidance used in these experiments

- [Dehnert and Stepanov, *Fundamentals of Generic Programming*](https://www.stepanovpapers.com/DeSt98.pdf),
  introduction: discover common requirements across varied clients, separate
  types from operations, and test combinations of independent components.
  Minimizing the requirements of one theorem alone is insufficient evidence.
- [Parnas, *On the Criteria To Be Used in Decomposing Systems into Modules*](https://ckrybus.com/static/papers/decomposing_systems_into_modules_1972.pdf):
  organize boundaries around decisions that change independently. Test changing
  representation, evaluation or information without rewriting unrelated proofs.
  Hide representation details, but expose economically material assumptions.
- [The mathlib Community, *The Lean Mathematical Library*, section 4.1](https://leanprover-community.github.io/papers/mathlib-paper.pdf):
  equivalent bundled and unbundled mathematics can differ substantially in use.
  Test composition, inference and competing structures on a carrier against
  existing mathematical interfaces.
- [Ousterhout, *A Philosophy of Software Design*, chapter 6 extract](https://web.stanford.edu/~ouster/cgi-bin/aposd2ndEdExtract.pdf):
  assess useful functionality relative to interface complexity. In a proof
  library this includes what representation details and hypotheses a caller
  must understand, beyond the number of tactic lines.

These are heuristics, not rules requiring records, forbidding records, or
justifying category instances before a client needs them.

## Priority order

1. **Semantic adequacy:** faithful scope, legitimate edge cases and informative
   counterexamples. No improvement obtained by silently changing the question.
2. **Useful expressiveness:** a named new theorem, model or operation becomes
   available. Universal encodability alone does not count.
3. **Actual reuse:** independent consumers use the same construction or proof
   without changing it. Identify their common requirement.
4. **Composition and change locality:** invariants survive composition; one
   representation or policy can change without global repairs.
5. **Interface quality:** discoverable names, local assumptions, predictable
   inference and transparent specializations where they help.
6. **Cost:** proof length, adapters, elaboration, dependencies and maintenance.
   A longer component can win through useful expressiveness or reuse.

Do not collapse these into an arbitrary numeric score. Record the tradeoff and
the strongest consumer. A second consumer is persuasive evidence, not a rule
excluding a substantive extension with one compelling application.

## Reassessment of the first comparisons

Guarded coverage establishes genuine cross-area reuse. Its larger footprint
does not refute its usefulness. The comparison did not establish a benefit
from forcing every native judgment to use that exact representation. Revisit
independent ownership when another consumer needs the guards or coverage.

Simulation composition retains richer data than verdict composition. Its value
is not settled by line counts against `Iff.trans`; test uses of the retained
maps and deviation witnesses.

## Broader coverage

| Direction | Discriminating consumer | Status |
| --- | --- | --- |
| Reduced incentive views | supporting utility/allocation slopes, payment theory, multi-unit quantities | MEC-007 starts here |
| Blocking proposals and coalitions | contracts, classical matching, strong Nash with exact scope | queued |
| Parametric choice | changing budgets, zero wealth, closed demand graph | MEC-001 to resume |
| Separate states and outcomes | typed blocking proposals without fabricated rewards | paired with blocking |
| Preferences over laws | non-expected-utility pure-deviation sufficiency | needs a named theorem |
| Information transformations | interim/ex-ante comparison with null-signal control | untested |
| Scales and identification | quantitative errors or welfare under independent recodings | partial GameTheory evidence |
| Certificate conversion | converting a composite certificate versus composing conversions | untested |

Stop a direction after representative consumers use established operations or
a counterexample narrows the proposal. Finite experiments cannot prove that no
better abstractions exist; they can support a coherent, tested collection and
expose remaining gaps.
