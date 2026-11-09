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
| `Equilibrium.Problem` | Validity, optimality, comparison transport, value recoding, exact morphisms and comorphisms |
| `Equilibrium.Expected` | Expected-value evaluation with integrable incumbents and deviations |
| `Equilibrium.Simulation` | Monotone value maps, deviation domination, composition, and compatible additive errors |
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
| `GameSimulation` | Every target deviation is bounded by a recoded legal source value; the incumbent bounds its recoding; validity is preserved |
| `MixtureSimulation` | Honest laws agree; every covered target deviation law is a probability mixture of legal source deviation laws |
| `ComparisonMixture` | One probability kernel mixes both laws of each source comparison to reproduce the target comparison |

`IsDeviationOptimal.of_comparisons` is the pointwise transport core. For every
admitted target deviation, it asks for a legal source deviation whose
nonimprovement implies target nonimprovement. The two problems may have different
value spaces equipped only with `LE`; no order laws or numerical recoding are
needed. Exact morphism and comorphism transport use this core.

`GameSimulation` is a stronger, numerical certificate. It supplies a Mathlib
order homomorphism `valueMap j : V →o W` for each target deviator. Its argument is

\[
v_Q(j,t) \le \varphi_j(v_P(g(j),s'))
\le \varphi_j(v_P(g(j),s)) \le v_Q(j,f(s)).
\]

`IsDeviationOptimal.of_dominated_deviations` states this argument at one
incumbent. `GameSimulation` packages it uniformly over incumbents. Source and
target values need preorders. Value maps are indexed by target deviators: two
target players represented by the same source player can use different scales.
Composition reindexes the inner value map by the outer deviator map, then
composes the order homomorphisms. Identity uses identity value maps.
`ofExactLifts` combines exact deviation lifts with recoded value equality;
exact reward-preserving morphisms convert using identity value maps.

A comorphism with the same state map supplies independent reflection, giving
an equilibrium iff at image states. This does not assert that every target
equilibrium has a source preimage.

## Value coordinates and additive errors

`EquilibriumProblem.mapValues P φ` changes each player's values from `V` to `W`,
leaving deviations and validity unchanged. Construction needs no order; identity
and successive recodings satisfy identity and composition laws. Monotone maps
preserve optimality and equilibrium. Maps preserving and reflecting comparisons,
such as order embeddings, give an iff without needing to be surjective. A
monotone constant map can create equilibria, so monotonicity alone gives no
reflection.

An exact morphism from `P.mapValues φ` to `Q` can be applied to
`h.mapValues hφ`, where `h` is a source equilibrium and `hφ` proves monotonicity.
This retains the numerical meaning of exact reward preservation. Simulations
also admit inequalities around the recoded values rather than requiring equality.
The comparison core covers transformations that do not factor through values:
an additive term constant along each player's legal deviations cancels from
those comparisons, even when it varies between different opponent profiles.

`transport_le_add` accepts source errors `ε : I → V` and target errors
`δ : J → W`. In addition to monotone target addition, it needs the pointwise bound

\[
\varphi_j(v_P(g(j),s)+\varepsilon_{g(j)})
\le \varphi_j(v_P(g(j),s))+\delta_j.
\]

Only the incumbent value is used. Identity maps preserve the same error. A real
affine map with slope `a > 0` and any offset transforms `ε` into `a * ε`;
arbitrary monotone maps provide no numerical error bound by themselves. No
additional approximate-equilibrium predicate is introduced.

## Characterization and categorical interpretation

Preserving a fixed game's equilibria observes less than preserving incentives.
Different rankings of suboptimal alternatives may leave the equilibria unchanged.
`preserves_comparisons_iff_forall_deviation_subsets` gives a precise stronger
characterization: at a fixed incumbent, a change of values preserves every
admissible nonimprovement comparison if and only if it preserves optimality
under **every restriction of the deviation relation**. Both sides retain the
same states and players. Candidate validity is deliberately absent from this
optimality statement; an invalid incumbent would make equilibrium preservation
vacuous. The reverse implication tests one deviation at a time.

The categorical interpretation fixes an observation before choosing morphisms.
Writing `E(P)` for the equilibrium subset of candidate states, preservation says
`f(E(P)) ⊆ E(Q)`. Together with identity and composition, restriction of state
maps to equilibria makes `E` a subfunctor of the state assignment. The inclusions
of equilibrium subsets form a natural transformation. Preservation plus
reflection gives `E(P) = f⁻¹(E(Q))`: the square of inclusions is a pullback. This
does not imply that `f` is invertible or that all target equilibria are in its
image. On a category of preserving and reflecting maps, the inclusion is a
cartesian natural transformation. These statements describe the proved transport
laws; the library does not add category instances.

Best-response preservation is a related, stronger observation for strategic
games. Hedges (2017) uses best-response-preserving morphisms for open games.
Tewolde and Conitzer (2024) study transformations universally preserving mixed
Nash or best-response sets; their positive-affine characterization assumes a
specified class of separable transformations. None of our numerical or law
certificates is claimed to characterize every equilibrium-preserving map.

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

Value recoding after expectation, `φ(∫ u)`, differs from changing outcome utility
before expectation, `∫ φ(u)`. `mapValues` performs the former and retains the
original integrability conditions. The latter uses a new expected-value problem
whose admissible deviations and valid incumbents may also change. For probability
laws and integrable real utilities, positive affine transformations commute with
expectation. Arbitrary increasing transformations generally do not. A sure `1`
and a fair lottery over `0, 2` have equal means, but cubing outcomes gives means
`1, 4`. The utility-independent law certificate can still be evaluated at new
integrable utilities; its source-equilibrium premise must concern that evaluation.

`isEquilibrium_ofExpectedValue_affine_iff` proves invariance under positive affine
changes of real outcome utilities for probability laws. It needs no global
integrability assumption: nonzero scaling and translation preserve integrability,
and expectation identities are used only at valid incumbents and admitted
deviations. At a nonintegrable state the total Bochner integral defaults to zero,
so even affine transformations need not identify the entire value records.

## Observations and approximate laws

`MixtureSimulation` requires equality of the observed outcome laws, often called
perfect indistinguishability. The requirement is local to compiled incumbents and
their covered deviations. Equality concerns `O`, the outcomes read by utilities;
`mapOutcome` permits a common measurable observation that forgets irrelevant
detail. Equal laws give equal evaluations for every common integrable utility.

A class of observable tests specifies which distinctions a weaker certificate
would retain. Agreement against all bounded measurable utilities already
characterizes equality of probability laws, since indicator functions test every
measurable event. Restricting tests only weakens a contract if the remaining
tests no longer separate the laws. Even bounded increasing tests separate
probability laws on real outcomes, through indicators of upper rays. One-sided
comparison against increasing utilities instead expresses stochastic dominance.
Comparison against every bounded measurable utility in both signs forces equality.

Composition does not require exact equality: numerical domination already
composes here, and suitable ordered or approximate law contracts can also compose.
For a fixed test class, transitivity alone composes agreement or
indistinguishability certificates. Closure under precomposition is a separate
condition when changing observations. Expressiveness is another condition:
GameTheory's `SecureImplementation` composes by transitivity, while its
`ContainsMeanTests` hypotheses make the selected tests sufficient for pseudo-Nash
transport. The current library supplies no test-class or approximate-law certificate.

For probability laws and bounded measurable real utilities, define total variation by
`d(μ, ν) = sup_A |μ(A) - ν(A)|` over measurable events. If `m ≤ u ≤ M`, the
expectation error is at most `d(μ, ν) * (M - m)`; for signed bounded utilities this
gives `2 * d(μ, ν) * ‖u‖∞`. An equilibrium transport may incur both a deviation
error and an incumbent error, which add. Exact incumbent-law agreement removes
the latter error. Approximate simulation budgets also require an explicit
composition rule; triangle inequalities and contraction under Markov kernels
give additive budgets in the total-variation setting. These bounds explain the
additional data an approximate extension would need; they are not theorems of
the present exact-law API.

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
- Monotone value maps compose across different value spaces and player sets.
- Affine scaling changes additive errors, and a monotone collapse can create equilibria.
- A deviation-constant offset preserves comparisons without any global value map.
- Recoding an expected payoff differs from recoding utilities before integration.

The Dirac theorem uses finite player sets and arbitrary action spaces with
measurable singletons. It compares exactly the integrable deviations admitted
by `mixedNashProblem`.

Infinite or undefined expected values remain outside these transport results.
Coalition preservation needs one source replacement bounding all members
simultaneously; separate scalar witnesses do not establish it. Arbitrary
solution concepts, quantitative law approximation, and computational
indistinguishability require their own compatibility results.

## References

- Jules Hedges (2017), *Morphisms of open games*.
  [arXiv:1711.07059](https://arxiv.org/abs/1711.07059).
- Emanuel Tewolde and Vincent Conitzer (2024), *Game Transformations That
  Preserve Nash Equilibria or Best-Response Sets*, IJCAI, pp. 2984–2993.
  [DOI: 10.24963/ijcai.2024/331](https://doi.org/10.24963/ijcai.2024/331).

## Provenance

The development adapts proof ideas and boundary cases from
[GameTheory's utility simulations](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Core/UtilitySimulation.lean),
[law simulations](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Core/MixtureSimulation.lean),
and
[incentive comparisons](https://github.com/elazarg/GameTheory/blob/6f1af625b77215dd9e4454e6120275dbd8b61f51/GameTheory/Analysis/IncentiveSimulation.lean).
The implementation uses MathEconLib's existing games and Mathlib's measure
theory. These bridges are internal MathEconLib results, not cross-library
equivalences or a dependency on GameTheory.
