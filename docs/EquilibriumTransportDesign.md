# Equilibrium transport architecture

The public root is
[`MathEconLib.GameTheory.Equilibrium`](../MathEconLib/GameTheory/Equilibrium.lean).
The strategic applications are available through
[`Strategic.Mixed.Transport`](../MathEconLib/GameTheory/Strategic/Mixed/Transport.lean)
and
[`Strategic.Outcome.Transport`](../MathEconLib/GameTheory/Strategic/Outcome/Transport.lean).
All are exported by `MathEconLib`. The Lean declarations are authoritative for
exact statements and hypotheses.

## Layers

| Module | Responsibility |
| --- | --- |
| `Equilibrium.Problem` | Candidate validity, deviation optimality, equilibrium, exact morphisms and comorphisms |
| `Equilibrium.Expected` | Expected-value evaluation with integrable incumbents and deviations |
| `Equilibrium.Simulation` | Pointwise domination, preservation, composition, reflection with a separate comorphism, and additive slack |
| `Equilibrium.Averaging` | Ordered averaging and scalar dominating witnesses |
| `Equilibrium.ComparisonMixture` | Shared mixtures of prescribed and alternative laws, independently of game structure |
| `Equilibrium.Mixture` | Utility-independent law simulations, composition, evaluation, and the fixed-incumbent comparison bridge |
| `Strategic.Basic`, `Strategic.Outcome`, `Strategic.Mixed` | Unilateral deviations, stochastic outcome evaluation, and independent mixed Nash |
| `Strategic.Mixed.Transport`, `Strategic.Outcome.Transport` | Pure-to-mixed Nash, mixed-source law transport, and stochastic outcome-game transport |

The existing `EquilibriumProblem`, `StrategicGame`, `OutcomeGame`, and
`PayoffStructure` own the game semantics. Measures, probability measures, and
kernels are Mathlib's carriers. No alternative equilibrium predicate or
probability representation is introduced. Generic product-order support and
the conversion from measurable probability-measure families to Markov kernels
live in `ForMathlib`.

## Admissibility and expected values

Candidate validity constrains the incumbent. An admissible deviation to an
invalid target still counts against equilibrium. `IsDeviationOptimal` isolates
the payoff inequalities from candidate validity.

`IsUnilateralDeviation` is the shared profile relation: one player replaces
their action while every other player's action remains fixed. It is used by
pure Nash, mixed Nash, and stochastic outcome Nash.

`EquilibriumProblem.ofExpectedValue D L u` evaluates a relation `D` using a
family of measures `L` and utilities `u` in a real Banach space:

| Component | Definition |
| --- | --- |
| Value at `s` for `i` | The integral of `u i` against `L s` |
| Admitted deviation from `s` to `t` | `D i s t` and integrability of `u i` against `L t` |
| Valid incumbent `s` | Integrability against `L s` for every player |

The constructor needs no measurable structure on states, no measurability of
the family of measures, and no global boundedness or measurability of utilities.
Integrability is checked against the individual laws used by the problem.
Completeness of the payoff space ensures that integrable Bochner values have
their expected interpretation. General measure families are permitted;
probabilistic outcome-game applications supply probability measures.

`mixedNashProblem` specializes this constructor to the independent product
law. Both `nashProblem` and `mixedNashProblem` retain their full defining
records: the tests check each record by `rfl`, including the mixed value
function `G.mixedExtension.payoff`. Existing reduction equations are unchanged.
`OutcomeGame.expectedNashProblem` specializes it to the game's stochastic
outcomes and a `PayoffStructure`. This definition does not require measurable
action spaces or a measurable outcome map. Measurability enters
`OutcomeGame.toKernel`, where a uniform outcome kernel is needed.
`mixedNashProblem_eq_expectedNashProblem` identifies mixed Nash with this
construction on the existing mixed outcome game, including integrability.

## Preservation and reflection

Preservation translates source states by `f : S → T` and assigns each target
deviator a source deviator by `g : J → I`.

`PayoffStructure.reindex P g` pulls utilities back along that player map.
It commutes with expected utility and preserves measurability, boundedness,
and continuity. For an unbundled utility family the same operation is ordinary
function composition, `u ∘ g`; `reindex_payoff` connects the two representations.

| Contract | Required correspondence |
| --- | --- |
| `GameMorphism` | Target deviations lift exactly to source deviations; corresponding values agree; validity is preserved |
| `GameComorphism` | Source deviations map to target deviations; corresponding values agree; validity is reflected |
| `GameSimulation` | Every target deviation is bounded by a legal source deviation; the incumbent value weakly increases; validity is preserved |
| `MixtureSimulation` | Honest laws agree; every covered target deviation law is a probability mixture of legal source deviation laws |
| `ComparisonMixture` | One probability kernel mixes both laws of each source comparison to reproduce the target comparison |

Simulation fields need only a comparison relation. Transport and composition
use preorder laws; exact morphism and comorphism transport needs only `LE`.
The pointwise domination argument is

\[
v_Q(j,t) \le v_P(g(j),s') \le v_P(g(j),s) \le v_Q(j,f(s)).
\]

`IsDeviationOptimal.of_dominated_deviations` states this argument at one
incumbent. `GameSimulation` packages the hypotheses uniformly and supports
identity and composition. Exact morphisms convert to simulations.

A comorphism with the same state map supplies independent reflection, giving
an equilibrium iff at image states. This does not assert that every target
equilibrium has a source preimage. `transport_le_add` preserves the same
additive slack under monotone addition; it does not add an approximate
equilibrium predicate.

## Averaging and law evaluation

`IsDeviationOptimal.of_integral_bounds` replaces a dominating source point
with an integrable probability mixture of admissible source deviations.
Ordered integration proves preservation for ordered Banach payoffs with
compatible addition, scalar multiplication, and closed upper order intervals.
It does not require a componentwise dominating support point.

For real payoffs, Mathlib's mean-bound witness theorem supplies one admissible
source deviation with value at least the integral. Almost-sure admissibility
is included in the excluded null set. `GameSimulation.ofIntegralBounds` and
`MixtureSimulation.toSimulation` use this scalar selection. The selected
point need not reproduce the mixture's outcome law.

A law certificate is parameterized by bare relations `DP`, `DQ` and kernels
`LP`, `LQ`, independently of utilities. Evaluation against problems `P`,
`Q` needs the following adapters at the incumbent:

- Every deviation admitted by `Q` is covered by `DQ`.
- A source alternative satisfying `DP` and having integrable utility is
  admitted by `P`.
- Utility is integrable under each admitted target deviation's law.
- The translated incumbent is valid in `Q`.

Relation equality is unnecessary. Conditional source integrability follows
almost surely from target integrability and the kernel composition identity.
The pointwise transport lemmas require these conditions only at the incumbent;
constructing a global `GameSimulation` requires uniform conditions.

`transport_ofExpectedValue` supplies these adapters for the shared expected-value
construction, including validity from honest-law equality.
`transport_expectedNash` specializes it to `OutcomeGame` and
`PayoffStructure`, so callers need no separate payoff-representation proofs.
`transport_isMixedNash` applies this adapter to the canonical mixed outcome
game and consumes the existing `G.IsMixedNash` predicate. Its target is the
expected Nash problem of a stochastic outcome game on the original pure
profiles. The canonical mixed outcome game is automatically measurable;
no global payoff measurability assumption is introduced.

## Measurable simulation and composition

A `MixtureSimulation` selects

```lean
simulate : J → S → Kernel T S
```

and requires a Markov kernel for every fixed deviator and incumbent. This
selected measurable realization is stronger than pointwise existence of
representing probability measures. No joint measurability in the fixed
parameters or measurability of the incumbent compiler is required.

The observation kernels themselves may be general measure kernels.
Probabilistic games use Markov observation kernels. Honest-law equality alone
says nothing about whether a pointwise utility-preserving map is a law
simulation.

Composition mixes the selected simulation kernels. Source deviation sets must
be measurable to propagate almost-sure legality through composition.
For countably many players with measurable action singletons,
`measurableSet_isUnilateralDeviation` supplies this premise. Expected-value
adapters add integrability separately, so composition needs no measurable
integrability restriction on the bare relation.
`id` uses measurable deviation sets; `idOfMeasurableSingleton` supplies
identity on spaces with measurable singletons without that premise.
The two identity constructors are equal when both sets of premises are
available, and both have simplification laws for left and right composition.
Composition still requires measurable source deviation sets.
`ofExactLifts` uses measurable deterministic lifts and honest-law equality.
Discrete target spaces allow the exact morphism's existential lifts to be
selected measurably.

`mapOutcome` applies a common measurable observation to both outcome laws
while retaining the simulation witnesses. It makes the observed outcome
space explicit.

## Mixtures of comparisons

`ComparisonMixture` pairs prescribed and alternative laws and mixes both
with the same weights. Its preservation theorem assumes integrability of
the two actual target laws and source inequalities almost surely under the
selected mixture. Identity and composition retain this shared randomization.

Prescribed source laws may vary with the comparison. Consequently the
certificate supplies neither one source incumbent nor a deviation relation.
An equilibrium application must connect its source comparisons to admissible
deviations. `MixtureSimulation.toComparisonMixture` supplies this connection
at a fixed incumbent, where every prescribed source law is constant.
The comparison theory imports only Mathlib kernel integration; the bridge
belongs to the simulation module.

## Clients and boundaries

[`MathEconLibTest.GameTheory.Simulation`](../MathEconLibTest/GameTheory/Simulation.lean)
checks the public interfaces:

- An added coin action has no exact lift but admits domination and a law mixture.
- Stochastic outcome-game transport reuses the law certificate through the
  outcome and payoff adapters.
- An existing vector-valued mixed equilibrium transports to a randomized target
  with an additional outcome-irrelevant action component.
- A varying-prescribed-law comparison mixture has no matching prescribed
  source law at either source index.
- Local validity suffices even when global validity preservation fails.
- A bare law certificate covering a nonintegrable state still transports
  equilibrium through the admitted-deviation interface.
- A vector-valued pure equilibrium embeds into the genuine mixed Nash problem;
  a separate integrable vector mean has no dominating support point.
- Equal rewards do not ensure honest-law equality, and improving deviations
  to invalid targets still exclude equilibrium.

The Dirac theorem uses finite player sets and arbitrary action spaces with
measurable singletons. It compares exactly the integrable deviations admitted
by `mixedNashProblem`.

Infinite or undefined expected values remain outside these transport results.
Coalition preservation needs one source replacement bounding all members
simultaneously; separate scalar witnesses do not establish it. Arbitrary
comparison relations, quantitative law approximation, and computational
indistinguishability require their own compatibility results.

## Provenance

The development adapts proof ideas and boundary cases from
[GameTheory's utility simulations](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Core/UtilitySimulation.lean),
[law simulations](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Core/MixtureSimulation.lean),
and
[incentive comparisons](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Analysis/IncentiveSimulation.lean).
The implementation uses MathEconLib's existing games and Mathlib's measure
theory. These bridges are internal MathEconLib results, not cross-library
equivalences or a dependency on GameTheory.
