# Equilibrium information levels: MathEconLib survey

Nov 10, 2026 · @Elazar Gershuni

The core of `EquilibriumProblem` uses only one comparison per deviation, yet it is presented as a value function into a shared type. Each transport theorem on branch `design/equilibrium-simulations` genuinely needs a different, larger bundle, so the transport layer is already a level hierarchy, just not named as one.

**Scope.** This survey reads branch `design/equilibrium-simulations`. Upstream main also has explicit comparison relations (#281) and finite Afriat (#296). Evidence from GameTheory experiments (decisions D78–D92) is noted where it applies; MathEconLib-specific tests are on the Experiments tab.

## Vocabulary

An equilibrium check asks one thing per candidate: is there a move, owned by some judge, that the judge counts as a gain? Everything stored beyond that answer either enables more questions or enforces consistency. Six independent axes describe what is stored; the judgment ladder is the main one.

### Judgment ladder: how a move is judged

| Level | Stored information | First question it enables | Typical consumer |
| --- | --- | --- | --- |
| Verdict | a predicate on candidates | is this candidate an equilibrium? | nothing else |
| Menu | a choice function, menu to chosen subset | blocking by sets, substitutability | contract stability |
| Better-move | a relation "this move is profitable" | improvement paths | finite improvement property |
| Stay-vs-move | per judge, the incumbent compared with one deviation | no profitable deviation | Nash, DSIC, revelation principles |
| Pairwise | per judge, any two outcomes compared | best response, dominance, strictness | weak dominance |
| Order | Pairwise plus transitivity, totality or antisymmetry | chains, argmax | `GameSimulation`, deferred acceptance |
| Mixable | a relation on outcome laws that respects mixing; no numbers | closure under mixing, mixed dominance | correlated-equilibrium convexity |
| Score | values in an ordered type | monotone re-encoding of values | `mapValues` |
| Slack | values in an ordered additive monoid | ε-approximation | `transport_le_add` |
| Cardinal | values in ℝ or an ordered vector space | differences, scaling, integrals | envelope theorem, averaging |
| Expected | outcome laws plus a utility, combined by expectation | affine invariance, interim decomposition | `ofExpectedValue` |
| Law-only | outcome laws; the utility is quantified in the statement | "for every payoff" results | `MixtureSimulation` |

The ladder branches. Mixable needs no numbers, while Score, Slack and Cardinal add them; both branches meet at Expected. Law-only stores the same laws as Expected but removes the utility from the data, so a Law-only theorem implies the Expected one for every utility. Menu sits beside Better-move: a choice function judges sets of contracts, not single moves.

A type does not fix the level. `[LE V]` with no order laws can encode any Stay-vs-move relation, so a value function into such a `V` is Stay-vs-move data, not Score data.

### Other axes

| Axis | Options | Example |
| --- | --- | --- |
| Arena: where states and moves live | Shared arena (one type for candidates and deviation targets); Gated arena (one type plus a validity predicate on candidates); Split arena (separate candidate and outcome types); Moves-as-data (a type of moves per judge and candidate, with a target map) | reports versus outcomes in mechanisms |
| Gate: validity of candidates | integrability, feasibility, individual rationality, restricted report sets | `ofExpectedValue` gates on integrability |
| Judges: who evaluates a move | Players; Indexed judges (player × type, player × opponents' reports); Coalition moves (several judges on one move, unanimous gain required); Unjudged (one planner or seller) | BIC judges per (player, signal) |
| Sharing: what judges have in common | Private scales; Common scale (sums across players); Common score (one function for all: potential, team games) | revenue and welfare need a Common scale |
| Derivation: where moves and values come from | product decomposition of profiles; reports precomposed with strategies; values from outcome plus transfer | unilateral replacement in `Π i, A i` |
| Space: structure on states | topology, convexity, measurability, finiteness, lattice order, a 1-D type interval | Kakutani, Tarski, Myerson |

## EquilibriumProblem: presented versus used

`EquilibriumProblem` looks like Score data, a value function into one shared ordered type, but its core is Stay-vs-move. Paths are relative to `MathEconLib/` on branch `design/equilibrium-simulations`.

```lean
structure EquilibriumProblem (S : Type u) (I : Type v)
    (V : Type r) where
  deviation : I → S → S → Prop
  value : I → S → V
  valid : S → Prop
```

(`GameTheory/Equilibrium/Problem.lean:77`.) Three facts show that the value function is more than the core needs:

1. **The predicate reads values only in rooted pairs.** `IsDeviationOptimal` (`:95`) is `∀ i s', deviation i s s' → value i s' ≤ value i s`. No law of `≤` is required: only `[LE V]`.
2. **The core transport theorem only uses one comparison per deviation.** `of_deviation_comparisons` (`:106`) asks, for each target deviation, for a legal source deviation such that source non-improvement implies target non-improvement. The iff `preserves_comparisons_iff_forall_deviation_subsets` (`:197`) shows this is exactly what preserving optimality under every restriction of deviations means.
3. **A lawless `LE` encodes any rooted relation.** Given a gain relation `gain i s s'`, take `V := I × S` with `(i, s') ≤ (j, s)` iff `i = j ∧ ¬ gain i s s'`, and `value i s := (i, s)`. So the structure can express any Stay-vs-move problem, and nothing in the core rules this encoding out.

### The exact maps require more than their proofs use (checked)

`GameMorphism` and `GameComorphism` require `value_eq` in one shared `V`. Their proofs go through comparison transport and use `value_eq` only to rewrite the comparison:

```lean
theorem transport_isDeviationOptimal [LE V]
    (f : GameMorphism P Q) {s : S}
    (h : P.IsDeviationOptimal s) :
    Q.IsDeviationOptimal (f.toFun s) := by
  apply h.of_deviation_comparisons f.deviatorMap
  intro j t ht
  obtain ⟨s', hs', rfl⟩ := f.deviation_lifts j s t ht
  exact ⟨s', hs', fun hle ↦ by
    simpa only [f.value_eq] using hle⟩
```

(`Problem.lean:305`; `pullback_isDeviationOptimal` at `:360` is symmetric.)

**Alternatives.**

- Replace `value_eq` with "the matched comparison is preserved". The maps then work across value types, which `GameSimulation` already allows by a different route.
- Or keep the exact maps as the simple special case and document that the comparison-preserving map is the general notion.
- Separately, `V` is shared by all judges although nothing compares across judges in the core. `V : I → Type` would be Private scales; the cost is dependent types in every signature.

## Each transport theorem pins a level

The branch's transport layer already climbs the ladder one rung per tier: comparison matching at Stay-vs-move, simulation at Order, error bounds at Slack, averaging at Cardinal, mixtures at Law-only. Each row names the operation in the proof that forces its rung.

| Theorem | Anchor | Needs | What forces it | Note |
| --- | --- | --- | --- | --- |
| `of_deviation_comparisons` | `Equilibrium/Problem.lean:106` | Stay-vs-move; value types may differ | one comparison per matched pair | the principle every other row reduces to |
| `isDeviationOptimal_iff_not_lt` | `Problem.lean:128` | Order (linear) | `not_lt` | under a partial order, "≤" and "no strict gain" are different notions |
| `mapValues` preservation and iff | `Problem.lean:255`, `:268` | Score; the iff needs only an order embedding | monotonicity | equilibrium is invariant under re-encoding values |
| `GameMorphism.transport`, `GameComorphism.pullback` | `Problem.lean:313`, `:367` | Stay-vs-move | `value_eq` used only to rewrite | stated with equal values in one `V` |
| `GameSimulation.transport` | `Equilibrium/Simulation.lean:34`, `:103` | Order (`Preorder V`, `Preorder W`) | the chain t' ≤ φ(s') ≤ φ(s) ≤ t | the first row comparing outcomes neither of which is the incumbent |
| `transport_le_add` | `Simulation.lean:143` | Slack (`Add`, `AddRightMono`) | an explicit error bound | monotone φ alone does not preserve an error |
| `of_integral_bounds` | `Equilibrium/Averaging.lean:38` | Cardinal (ordered Banach, `ClosedIciTopology`); Space: measurable | `integral_mono_ae` | vector payoffs allowed |
| `ofIntegralBounds` | `Averaging.lean:72` | Cardinal on ℝ | picks a point at least the mean | an arrow from Cardinal down to Order |
| `isEquilibrium_ofExpectedValue_affine_iff` | `Equilibrium/Expected.lean:63` | Expected, ℝ utility | `integral_add`, scaling by a > 0 | cardinal invariance; the Gate is integrability |
| `MixtureSimulation.transport_ofExpectedValue` | `Equilibrium/Mixture.lean:320` | Law-only; Space: Markov kernels | `Kernel.integral_comp` | the certificate never mentions utility |
| `MixtureSimulation.toSimulation` | `Mixture.lean:297` | Law-only to Order | `exists_notMem_null_integral_le` | an arrow down the ladder |
| `ComparisonMixture.preserves_at` | `Equilibrium/ComparisonMixture.lean:85` | Law-only at one pair; Unjudged | — | a comparison-level primitive with no library client |
| `transport_isMixedNash`, `transport_expectedNash` | `Strategic/Mixed/Transport.lean:86`, `Strategic/Outcome/Transport.lean:36` | Law-only; Split arena | law simulation | judges reindexed by `deviatorMap` |
| `IsNash.isMixedNash_dirac` | `Strategic/Mixed/Transport.lean:37` | Cardinal; Space: measurable singletons | via averaging | pure Nash gives mixed Nash at Dirac laws |
| `dominatedActionSimulation` | `Strategic/Reduction.lean:48` | Order | domination | the finite-mixed variant (`:101`) needs Expected and finiteness |

**Reading the table.** Three tiers are earned by their proofs: simulation needs transitivity, error bounds need addition, averaging needs integrals. Two rows sit lower than stated: the exact maps (Stay-vs-move, stated with equal values) and `IsMixedNash` (Mixed.lean:184), whose definition needs only `[LE V]` although it is posed on a Banach space.

## Mechanism design and single-parameter theory

Incentive definitions and both revelation principles need only Stay-vs-move; the jump to Cardinal happens exactly where a proof adds two incentive constraints or integrates over types. Incentive constraints are judges with a large index, so the Judges axis carries most of the structure here.

| Item | Anchor | Needs | What forces it | Over-bundled? |
| --- | --- | --- | --- | --- |
| `IsDSIC` | `Mechanism/Core/SolutionConcepts.lean:66` | Stay-vs-move; Judges (i, θ, r); Moves-as-data (reports) | one rooted comparison | real quasilinear utility is not used |
| `isDSIC_iff_isDominant` | `Mechanism/Core/Strategic.lean:79` | Stay-vs-move (`LE V`) | dominance is Nash with judges indexed by opponents' profiles | — |
| `IsExPostIR` | `SolutionConcepts.lean:73` | Score plus a constant 0 | an outside option | a constraint, not a judgment |
| `IsBICOn` | `Mechanism/Core/BayesianIC.lean:66` | Expected; Judges (i, signal); Space: measurable | integral over the opponents' conditional law | quasilinearity unused, as its docstring says |
| `IsBIC.isBNE` | `BayesianIC.lean:98` | Expected | integrating interim inequalities | an arrow from (player, signal) judges to player judges |
| `revelation_principle_dominant` | `Mechanism/Core/Revelation.lean:74` | Stay-vs-move | report deviations map to action deviations | ℝ unused |
| `revelation_principle_bayesian` | `Revelation.lean:98` | Stay-vs-move via `GameComorphism.pullback` | measurability enters only through the deviation relation | — |
| `HasEnvelopeIC` and `integral_rep` | `SingleParameter/IC.lean:55`, `EnvelopeIC.lean:137` | Cardinal; Space: 1-D type order, Lebesgue measure | monotone allocation has countably many jumps; fundamental theorem of calculus | see the note below |
| `payment_identity` | `SingleParameter/Payment.lean:47` | Cardinal; Derivation: quasilinear | solves the utility identity for payment | — |
| `typeDeviationIC_of_monotone_q` | `Payment.lean:86` | Cardinal; Space: 1-D | integral bounded by a rectangle | — |
| `strictMonotonicity` | `Auction/StrictMonotonicity.lean:167` | universal IC over all bids, regularity, atomless types | type-deviation IC reaches only bids other types use | the larger move set is earned |
| `revenue_equivalence` | `Auction/RevenueEquivalence.lean:55` | Cardinal; independence, identical distribution, 1-D | equality between two mechanisms with IC as a hypothesis | may assume more than it uses; see below |
| `sellerProfit_eq_virtualSurplus` | `ValueDistribution/SellerProfit.lean:99` | Cardinal; Unjudged (seller) | integration against a density | an argmax, not a judgment |

### Note: envelope IC is not weaker than type-deviation IC

`HasEnvelopeIC` is documented as "the weakest IC condition used by the single-parameter development" (`SingleParameter/IC.lean:54`), with an instance from `HasTypeDeviationIC` proved by `linarith`. The reverse direction appears to hold by the same algebra, assuming payoff is `v · alloc − pay`:

```latex
\mathrm{payoff}(v, \sigma(v')) = U(v') + (v - v')\, q(v')
```

Then `(v − v') q(v') ≤ U(v) − U(v')` is the same inequality as `payoff v (σ v') ≤ payoff v (σ v)`. If so, the two conditions are equivalent, and the real difference is that envelope IC is Verdict-level data on the reduced pair (U, q), with no moves. That is exactly what the envelope theorem consumes. The reverse instance has not been written or checked in Lean.

### Note: revenue equivalence hypotheses

`revenue_equivalence` requires `[A₂.IsSymmetricIPV]`, which bundles a density and atomless types. The survey read suggests the proof uses only independence, bounded types and the identical-distribution hypothesis passed separately. This was not checked by building.

## Matching, choice and preferences

Matching theory runs on the Menu level, below any preference relation, and the preference files contain MathEconLib's explicit arrows between ladder rungs. One expected arrow, from choice back to preference, is missing.

### Matching

| Item | Anchor | Needs | What forces it |
| --- | --- | --- | --- |
| `IsBlockingPair`, `IsStableMatching` | `Matching/Classical/Marriage/Basic.lean:81`, `:100` | Coalition moves (pairs); Order (linear) per agent; Private scales (`Option W` for men, `Option M` for women) | both partners strictly prefer each other |
| `womenWeaklyPrefer_of_menWeaklyPrefer` | `Marriage/Basic.lean:234` | Order (linear): totality and antisymmetry | `lt_of_not_ge`, `le_antisymm` |
| `CompleteLattice StableMatching` | `Matching/Classical/StableOrder.lean:92` | Menu; Space: finite, Tarski | transported from the contracts fixed points |
| `galeShapley_manOptimal` | `DeferredAcceptance.lean:348` | Order (linear); Space: finite | round bound |
| contracts `Blocks`, `Stable` | `Matching/Contracts/Basic.lean:206`, `:212` | Menu; Gate (individual rationality) | every agent touching the blocking set picks its part from the union |
| `exists_stable`, `sellerOptimal` | `Contracts/StableFixedPoints.lean:555`, `:518` | Menu plus substitutability and the law of aggregate demand; Space: complete lattice | antitone operators, Tarski |
| `pairwiseStable_iff_stable_of_substitutable` | `Contracts/Basic.lean:284` | Menu plus substitutability | reduces blocking sets to single contracts: an arrow that shrinks the judge index |

Marriage stability is the Coalition-moves misfit. It fits `EquilibriumProblem` only with judges `M ⊕ W ⊕ M × W`, a sum value type, and a lawless "not both strict" `LE`. That relation is not transitive, so `GameSimulation` and everything above Stay-vs-move are lost.

### Arrows between ladder rungs

| Arrow | Anchor | From | To | Condition |
| --- | --- | --- | --- | --- |
| `IsRepresentedBy`, `ofUtility` | `Preferences/Representation/Basic.lean:55`, `:67` | Score | Order | always; the codomain may be any `Preorder`, so multi-utility representations fit |
| `exists_isRepresentedBy_nat` | `Representation/Finite.lean:42` | Order (complete) | Score in ℕ | finite type; utility = size of the lower contour set |
| `ofBundleOrder`, `maximizers` | `Choice/Induced.lean:88`, `Choice/Maximizers.lean:68` | Order | Menu | induced choice |
| `consistent_ofOptionLinearOrder_iff_hasBundleOptimum` | `Choice/Induced.lean:647` | Order | Menu | induced choice is consistent exactly when every menu has an optimum |
| `tieBreak` | `Choice/Refinement.lean:46` | Order (complete preorder) | Order (linear) | refinement |
| `ofIntegralBounds`, `MixtureSimulation.toSimulation` | see the transport table | Cardinal, Law-only | Order | ℝ values, integrability |

**Missing.** A countable or continuous (Debreu) representation theorem. Finite rationalizability exists: `garp_iff_exists_afriatCertificate_and_regularUtility` (#296).

## Concepts outside the one-step scheme

Coalition moves are the one misfit a library change could absorb; the others are constraints, maximizations or comparisons between mechanisms. GameTheory's D82 and D83 show that local comparability covers strong Nash, and that a matching displacement fits once consenting players and affected coordinates are separated.

| Concept | Anchor | What it is instead | Can it be made to fit? |
| --- | --- | --- | --- |
| `IsStrongNash` | `GameTheory/Strategic/Basic.lean:332` | for every profile change, some changer is weakly worse off | Only through a lawless coalition-tagged `LE`, which rules out `GameSimulation` |
| marriage and contract blocking | see Matching | several judges must agree on one move | as above; contracts fit naturally at Menu as a "blocking move" relation |
| `IsEfficient` | `Mechanism/Core/SolutionConcepts.lean:79` | an argmax of summed values | Unjudged with a Common scale; a judgment only if every outcome counts as a move |
| `IsBudgetBalanced`, `IsNoDeficit` | `SolutionConcepts.lean:92`, `:95` | constraints on transfers | Verdict with a Common scale; no judge |
| `IsExPostIR` | `SolutionConcepts.lean:73` | a comparison against a constant | Score plus a constant, or an "exit" move valued at 0 |
| `payment_equivalence`, `revenue_equivalence` | `Auction/Basic.lean:450`, `Auction/RevenueEquivalence.lean:55` | equalities between two mechanisms | not judgments; IC enters as a hypothesis |
| optimal pricing | `ValueDistribution/PostedPriceOptimality.lean:355` | an argmax over a one-parameter family | Unjudged |

## Design options for MathEconLib

The branch's transport theorems already assume different amounts; the options below make that explicit and remove the places where a statement asks for more than its proof uses. Each notes the related evidence. They are ordered by how much existing code they touch.

1. **Name the levels in the documentation.** State, in the module docs of `Equilibrium/`, that `EquilibriumProblem` is Stay-vs-move data and which rung each transport file needs. No code changes.
2. **Comparison-preserving maps.** Replace `value_eq` in `GameMorphism` and `GameComorphism` with preservation of the matched comparison, or add that notion beside them. The proofs already work this way. Main has `transportWith` and `pullbackWith` beside the maps, with `value_eq` kept.
3. **Drop unused algebra from definitions.** `IsMixedNash` and `bneProblem` need only `[LE V]`; pure existence (`Strategic/Existence.lean:606`) needs only a linear order on values. Move the Banach and ordered-module requirements to the theorems that use them.
4. **First-class coalition moves.** A move that carries its coalition, judged by strict unanimity. Strong Nash, marriage stability and contract blocking would share it. *Evidence:* GameTheory needs no such structure for strong Nash or the tested matching case; local comparability suffices (D82, D83).
5. **A relation-valued problem.** Make `EquilibriumProblem` the Score-level instance of a relation-level structure, with a forgetful map that preserves equilibria. Main's explicit comparison relations (`IsOptimalWith`, #281) sit on the existing record instead and cover most of this.
6. **Fill the missing arrows.** Finite rationalizability exists (#296); a countable or continuous representation theorem is missing.

GameTheory already stores a bare `Ranking` and applies it only to rooted pairs, so options 4 and 5 would bring the two libraries' cores to the same level.

## Method and unverified items

About 60 MathEconLib definitions and theorems were classified by reading their statements and proofs on branch `design/equilibrium-simulations`; nothing was built. The sample covers `GameTheory`, `Mechanism`, `Auction`, `SingleParameter`, `ValueDistribution`, `Competition`, `Matching`, `Choice` and `Preferences`. A companion survey of GameTheory uses the same vocabulary.

Checked directly for this report: the `EquilibriumProblem` fields, the morphism and comorphism proofs, the `HasEnvelopeIC` docstring and forward instance, the `revenue_equivalence` signature, and the anchors of `IsDSIC`, `revelation_principle_dominant`, `isEquilibrium_ofExpectedValue_affine_iff` and `exists_isNash_of_quasiconcaveOn`. The following rest on the survey reads and should be confirmed before acting on them:

- that envelope IC implies type-deviation IC in Lean (the algebra above suggests it; no proof was written);
- that `revenue_equivalence` uses less than `IsSymmetricIPV`;
- that `IsMixedNash` and `bneProblem` use no algebra in their definitions;
- the remaining line numbers in the evidence tables, collected by the survey agents.
