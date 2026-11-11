# Abstraction analysis

A solution concept is a verdict on candidates, and everything a library stores beyond that verdict buys either more questions or more consistency. This tab gives the library-neutral analysis; the Survey evidence tab holds the MathEconLib item tables it draws on.

## Evidence from GameTheory experiments

The invariance test holds up under testing, and no level of the ladder needs a structure of its own in the clients tested. The evidence is 14 GameTheory experiments, recorded as decisions D78–D92 in `GameTheory/docs/decisions/`; MathEconLib-specific tests are on the Experiments tab.

| Claim | Evidence | Consequence for MathEconLib |
| --- | --- | --- |
| State a result at the lowest level that passes the invariance test | D78, D79: the Kuhn and Bayesian bridges and response dynamics hold for any preference over outcome laws | `StrategicGame` takes any `LE V`; mixed and Bayesian games fix a Banach-space `V` |
| Incumbent evaluability, deviation evaluability and menu membership are three predicates | D81 | the mixed and Bayesian problems put deviation integrability inside `deviation`; `valid` covers only the incumbent |
| There is no single Mixable level | D80: two-way mixing closure does not give countable closure. D89: weak mixture preservation is weaker than independence | averaging and law-simulation certificates should state the mixture law they use |
| Dynamic consistency needs a composition law; expected utility is one instance | D89 | no MathEconLib client |
| Comparability at the incumbent and its replacement relates the weak and strict readings | D79, D82 | `isStrongNash_iff_not_lt` assumes a global `LinearOrder` |
| No judgment level needs its own structure in the tested clients | D92 | certificates can stay theorem hypotheses until a client chains them |
| A generic transport theorem need not be mandatory | D78: direct bridge proofs were 4–5 lines shorter | bridges may keep direct proofs |
| Welfare needs an explicit Common scale | D85: rescaling one person's utility changes a welfare maximizer | efficiency statements keep their sum explicit |

Each claim rests on one GameTheory experiment, usually a single machine-checked counterexample or client. The counterexamples transfer to MathEconLib; the design choices need MathEconLib evidence.

## The invariance test

A statement belongs at the lowest level whose admissible re-encodings leave its truth unchanged. This is measurement theory's scale types applied to solution concepts, and it gives a mechanical way to place a theorem.

The levels differ along two kinds of dimension. Relational levels differ in **domain** (which pairs are compared: rooted pairs only, or all pairs) and in **laws** (transitivity, totality, mixing axioms). Numeric levels differ in their **invariance group**: the re-encodings of values that every statement at the level must survive.

| Level | Admissible re-encodings of a judge's data | Invariant statements | First statement that fails |
| --- | --- | --- | --- |
| Stay-vs-move | any change that keeps each incumbent-versus-deviation comparison | Nash, DSIC, revelation principles | best response among options that are not the incumbent |
| Pairwise, Order | any change that keeps every comparison | best response, dominance, stable matching | anything about how much better |
| Score | a strictly increasing map per judge | pure Nash in any order (`mapValues`) | ε-Nash |
| Slack | translations per judge, with ε fixed | ε-Nash, error-bound transport | statements that scale values |
| Cardinal | a·u + c with a > 0, per judge | weak monotonicity, Groves truthfulness | cross-judge sums without a Common scale |
| Expected | a·u + c with a > 0, applied before expectation | mixed Nash, Bayes–Nash | none within one judge |
| Law-only | any utility | Kuhn law equality, law simulations | — |

### Three worked failures

1. **Mixed Nash is not ordinal.** A player compares a sure outcome B with the lottery ½A + ½C. With u(A) = 0, u(B) = 1, u(C) = 3 the lottery wins (1.5 > 1). The strictly increasing re-encoding u(C) = 1.5 keeps the order A < B < C but now B wins (1 > 0.75). An equilibrium that relied on the lottery disappears, so mixed Nash needs Expected. MathEconLib's `isEquilibrium_ofExpectedValue_affine_iff` (`GameTheory/Equilibrium/Expected.lean:63`) and GameTheory's `representsExpectedUtility_unique_positiveAffine` (`Core/VNM.lean:207`) are exactly the statements that Expected's group is the positive affine group.
2. **ε-Nash is not ordinal.** Cubing all values preserves every comparison but turns a gap of 0.5 into 0.125 (from base 0) or 2.375 (from base 1), so whether the gap is at most ε changes. ε-Nash needs Slack; this is why `transport_le_add` (`GameTheory/Equilibrium/Simulation.lean:143`) needs an explicit error bound that a monotone φ alone cannot provide.
3. **Welfare is not per-judge affine-invariant.** Doubling one player's utility changes which outcome maximizes the sum. Efficiency, revenue and price-of-anarchy statements need a Common scale, an axis choice, not just Cardinal.

The test also explains the over-bundling found in the surveys: a statement typed with ℝ whose truth survives every strictly increasing map is stated at Cardinal but lives at Score or below.

## Each level as an interface

Each level is worth a name only if it has its own notion of map between problems; the table shows that every level used by the surveys does. A map at a higher level is automatically a map at every lower level, which is what lets a lower-level transport theorem serve all higher ones.

| Level | Data per judge | Consistency it enforces | Questions it unlocks | Its notion of map | Evidence |
| --- | --- | --- | --- | --- | --- |
| Stay-vs-move | moves and a gain relation rooted at the incumbent | none | is the candidate stable? | match each target move with a source move whose no-gain implies the target's | `of_deviation_comparisons` |
| Pairwise | a relation on all outcomes | comparisons exist between non-incumbent outcomes | best response, dominance, strictness | outcome maps that preserve the relation | weak dominance in `Strategic/Basic.lean:179` |
| Order | Pairwise plus laws | no preference cycles; finite sets have best elements | chains, argmax, opposition of interests | as Pairwise; domination chains compose | `GameSimulation` needs `Preorder` |
| Mixable | a relation on outcome laws plus a chosen mixture law: bound closure, comparison preservation or no-strict-gain closure, over finite or countable mixtures | only what the chosen law states; two-way mixing does not give countable mixing (D80) | closure under mixing, mixed dominance | maps of laws that commute with mixing | not present in MathEconLib; GameTheory's `Preference.Convex` |
| Score | values in an ordered type | representability by a single number line per judge | monotone re-encoding | a monotone φ per judge | `mapValues`, `GameSimulation` |
| Slack | values in an ordered additive monoid | additive gaps are meaningful | ε-approximation | monotone φ plus an error bound | `transport_le_add` |
| Cardinal | values in ℝ or an ordered vector space | intensity of preference is meaningful | differences, envelope, integrals | positive affine maps; integral bounds | averaging, `ofIntegralBounds` |
| Expected | outcome laws plus a utility | local gains compose through bind; sufficient for dynamic consistency, not necessary (D89) | interim decomposition, affine invariance | kernels that preserve expectations | `ofExpectedValue`, `IsBIC.isBNE` |
| Law-only | outcome laws only | none on utility | results for every payoff | law equality or a law simulation | `MixtureSimulation` |

### Minimal Lean shapes

These are sketches of what each level would store, not compiled code, and not proposals to add four structures. They make the information content explicit.

```lean
-- Stay-vs-move: moves and a rooted gain
structure RootedProblem (C O J : Type*) where
  move : J → C → O → Prop
  gain : J → C → O → Prop

-- Pairwise: any two outcomes compared
structure PairwiseProblem (C O J : Type*) where
  move   : J → C → O → Prop
  stay   : C → O
  weakly : J → O → O → Prop

-- Score: values in an ordered type
structure ScoreProblem (C O J V : Type*) where
  move  : J → C → O → Prop
  stay  : C → O
  value : J → O → V

-- Expected: outcome laws and a utility
structure ExpectedProblem (C J Ω V : Type*)
    [MeasurableSpace Ω] where
  move    : J → C → Measure Ω → Prop
  stay    : C → Measure Ω
  utility : J → Ω → V
```

Order and Mixable add laws as hypotheses on `weakly`; Slack and Cardinal add instances on `V`; Law-only drops `utility` and quantifies over it in statements. `EquilibriumProblem` is `ScoreProblem` with `C = O = S` plus a `valid` Gate, and its theorems mostly use only the `RootedProblem` content.

## Forgetful maps and representation theorems

Moving down the ladder always works and loses information; moving up needs a representation theorem with hypotheses, and that is where much of economic theory lives.

&#91;embedded content: judgment ladder · forgetful maps and representation theorems\]

Every forgetful map must preserve the verdict, so a theorem proved at a lower level applies after forgetting. Each upward arrow carries its own hypotheses.

| Arrow | Direction | Hypotheses | Where | Status |
| --- | --- | --- | --- | --- |
| Order to Score (ordinal representation) | up | complete preorder on a finite type | MathEconLib `exists_isRepresentedBy_nat`, `Preferences/Representation/Finite.lean:42` | finite only; countable and continuous (Debreu) versions are missing everywhere; EconCSLib defines `RepresentsPreference` with no existence theorem |
| Order and Mixable to Expected (vNM) | up | independence, continuity, finite outcomes | GameTheory `vnmAxioms_iff_exists_representsExpectedUtility`, `Core/VNM.lean:1120`; uniqueness up to positive affine at `:207` | present for finite outcomes in GameTheory only; EconCSLib has the axioms and their independence (`Foundation/Utility/VNMAxioms.lean:417`) |
| Menu to Order (revealed preference) | up | WARP on all finite menus; GARP on finite budget data | MathEconLib `garp_iff_exists_afriatCertificate_and_regularUtility` (`RevealedPreference/Afriat.lean:115`, #296); GameTheory `Math.FiniteChoice` (D84); EconCSLib only as the private `revealedRel` | finite cases present; restricted budgets can leave the order unidentified (D90) |
| Expected to Score | down | integrability, handled as a Gate | MathEconLib `ofExpectedValue` | present |
| Expected to Mixable | down | none | GameTheory `vnmAxioms`, `Core/VNM.lean:194` | present |
| Score to Order | down | none | MathEconLib `IsRepresentedBy`, `ofUtility` | present |
| Order to Menu | down | consistency needs an optimum in every menu | MathEconLib `ofBundleOrder`, `consistent_ofOptionLinearOrder_iff_hasBundleOptimum` | present |

### A third kind of arrow: certificate conversions

Some theorems convert a transport certificate at one level into a certificate at another, rather than converting problems. `GameSimulation.ofExactLifts` turns an exact morphism into a simulation. `MixtureSimulation.toSimulation` turns a Law-only certificate into an Order certificate for real values. `ofIntegralBounds` turns a Cardinal averaging bound into a domination certificate. These are maps between notions of map, and they are what lets a certificate found at the most convenient level feed the transport theorem of another.

## Weak versus strict primitives

All three libraries make the weak relation primitive ("the deviation is no better than staying"), and that choice is why coalition moves fit none of their order-level machinery. The strict relation ("the deviation is a gain") composes where the weak one does not.

| Library | Primitive | Anchor |
| --- | --- | --- |
| MathEconLib | `value i s' ≤ value i s` | `GameTheory/Equilibrium/Problem.lean:95` |
| GameTheory | `weaklyPrefers who (law of status quo) (law of deviation)` | `Core/Deviation.lean:126` |
| EconCSLib | `≤` on payoffs under `[Preorder U]` | `GameTheory/StrategicGame/NashEquilibrium.lean:28` |

For one judge with a total order the two forms agree: s' ≤ s exactly when not s < s'. They split in two situations.

1. **Partial orders.** With vector payoffs, an incomparable deviation breaks a weak-form equilibrium but not a strict-form one. `isDeviationOptimal_iff_not_lt` (`Problem.lean:128`) holds only under a linear order, so vector payoffs inherit the weak reading by default.
2. **Coalition moves.** A coalition blocks when every member strictly gains. That strict Pareto relation is transitive. Its weak counterpart, "some member is not better off", is not.

### Why the weak coalition relation is not transitive

Take two members and three outcomes with u₁ = (x: 2, y: 3, z: 1) and u₂ = (x: 2, y: 0, z: 1). Then:

- x does not beat y for everyone (member 1 prefers y);
- y does not beat z for everyone (member 2 prefers z);
- but x beats z for both members.

So "not blocked" fails transitivity, and encoding coalition stability as a single weak `≤` on a sum value type cannot give a `Preorder`. This is why `IsStrongNash` (`GameTheory/Strategic/Basic.lean:332`) is not built on `EquilibriumProblem`, and why marriage stability fits it only through a lawless `LE` that rules out `GameSimulation`. GameTheory's `Preference.coalition` ("some member weakly prefers") works with its `IsEquilibrium` only because that predicate needs no laws.

### The current coalition patterns do not share a notion

| Pattern | Library | Encoding |
| --- | --- | --- |
| strong Nash | MathEconLib | standalone predicate |
| strong Nash | GameTheory | "some member weakly prefers" aggregator on `Ranking` |
| blocking pair | all three | two strict comparisons conjoined |
| contract blocking | MathEconLib | choice functions on menus |
| transferable-utility core | GameTheory, EconCSLib | a sum inequality; the coalition collapses to one judge |
| Pareto optimality | EconCSLib fair division | grand coalition, weak for all and strict for one |

### A strict-primitive shape

A sketch, not compiled: moves carry their coalition, members keep private relations, and blocking is strict unanimity.

```lean
structure CoalitionProblem (C O A : Type*) where
  move    : Finset A → C → O → Prop
  stay    : C → O
  prefers : A → O → O → Prop  -- weakly

def CoalitionProblem.Blocks (P : CoalitionProblem C O A)
    (S : Finset A) (c : C) (o : O) : Prop :=
  P.move S c o ∧ ∀ a ∈ S,
    P.prefers a o (P.stay c) ∧ ¬ P.prefers a (P.stay c) o

def CoalitionProblem.IsStable (P : CoalitionProblem C O A)
    (c : C) : Prop :=
  ∀ S o, ¬ P.Blocks S c o
```

Singletons recover Nash, pairs recover blocking pairs, and transferable utility is the special case where each coalition is replaced by one judge with summed values.

## How the axes force levels

The axes are independent as data, but several axis options force a minimum judgment level, and that coupling is where most genuine level requirements come from. The table lists every coupling the surveys found.

| Axis option | Minimum level forced | Why | Evidence |
| --- | --- | --- | --- |
| Sharing: Common scale | Cardinal on one value type | sums across judges | efficiency and revenue (MathEconLib), VCG (GameTheory, EconCSLib), transferable-utility core |
| Sharing: Common score, exact | Slack | differences of the potential | `IsExactPotential` (GameTheory, EconCSLib) |
| Sharing: Common score, ordinal | Score with a linear order and finite range | a maximum of the potential exists | `IsOrdinalPotential.exists_isNash` (GameTheory) |
| Judges: change of index, ex-ante to interim | Expected | division by the type-fibre mass | `IsBIC.isBNE` (MathEconLib), `isNash_iff_interim` (GameTheory) |
| Judges: Coalition moves | Order per member, plus comparability at the incumbent and its replacement | weak and strict readings agree only where members can compare (D82) | see Weak versus strict primitives |
| Arena: mixed moves | Mixable | "pure deviations suffice" needs bound closure under the actual deviation laws, not two-way mixing (D80) | `isNash_mixed_iff` (GameTheory) |
| Arena: Shared arena for dynamics | Better-move | improvement paths chain outcomes | `ImprovingStep` (GameTheory) |
| Gate: integrability | Expected | only expectations can be undefined | `ofExpectedValue` (MathEconLib), `IsFeasibleICIRIntegrable` (EconCSLib) |
| Derivation: quasilinear values | Cardinal | two IC constraints are added so payments cancel | weak monotonicity, payment identity |
| Derivation: game tree with chance, one-shot principle | Expected | local gains compose through bind | one-shot deviation principle (GameTheory) |
| Space: Kakutani for pure strategies | Score with a linear order, plus quasiconcavity | convex best-reply sets | `exists_isNash_of_quasiconcaveOn` (`Strategic/Existence.lean:606`) |
| Space: 1-D type interval with a measure | Cardinal | fundamental theorem of calculus | envelope theorem, Myerson |
| Space: Tarski | Menu or Order, with a lattice | monotone operators | stable matchings (MathEconLib, EconCSLib) |

Two couplings matter most for design. A Common scale is the only route to welfare and revenue statements, so it should be an explicit parameter, not a consequence of choosing ℝ. And an index change of judges is where expected utility is genuinely spent; everything stated per judge before the change can stay lower.

## Encodings: the same information, packed differently

The three libraries store comparable information but pack it differently, and the packing, more than the information, decides which levels a library can express. The single most consequential choice is whether an outcome layer sits between strategies and values.

| Choice | Options seen | Where | Consequence |
| --- | --- | --- | --- |
| Outcome layer | strategies to outcome laws to preferences; or strategies straight to numbers | MathEconLib both (`OutcomeGame`, and `EquilibriumProblem` values); GameTheory `GameForm` (`play : Profile → PMF Outcome`); EconCSLib `payoff : Profile → N → U` | without outcomes there is nothing to quantify a utility over, so Law-only and Mixable cannot be stated at the game level |
| Where order laws live | named hypotheses on a bare relation; a typeclass on the value type; a field of the structure | GameTheory `Ranking` with `Transitive` as a hypothesis; MathEconLib and EconCSLib `[Preorder U]`; EconCSLib `Pref.prop : IsPreference` | hypotheses allow many relations on one type; typeclasses give Mathlib lemmas but one order per type; fields bundle laws with data |
| Lawless carrier | `[LE V]` with no laws | MathEconLib `EquilibriumProblem` | one structure covers Stay-vs-move, but the type suggests Score |
| Per-judge scales | one value type shared by all judges; a relation indexed by judge | MathEconLib and EconCSLib share `V`/`U`; GameTheory indexes `Ranking` by agent | sharing a type looks like a Common scale even when no statement compares across judges |
| Deviations | a relation; `Function.update` on a product; move types with an action | MathEconLib `deviation`, EconCSLib `IVariant`; EconCSLib strategic `deviate`; GameTheory `DeviationScheme.Dev` | only move types express correlated equilibrium (moves are maps of recommendations) and count moves; `update` hard-wires unilaterality |
| Validity | a predicate field; subtype moves; per-domain `feasible` fields | MathEconLib `valid`; GameTheory perturbed schemes; EconCSLib `SocialChoice.Instance.feasible` | a predicate lets a map state preservation or reflection as a separate condition; a subtype makes every map carry the proof |
| Probability carrier | `Measure` with kernels; `PMF`; the finite simplex | MathEconLib; GameTheory; EconCSLib `Lottery 𝕜 O := stdSimplex` | `Measure` brings an integrability Gate; `PMF` needs extended expectations; the simplex fixes finite outcomes and an ordered field |
| Generic interface or bridges | one problem structure with maps; one equilibrium predicate; per-domain structures with bridge functions | MathEconLib `EquilibriumProblem`; GameTheory `IsEquilibrium`; EconCSLib `GameTree.toStrategicGame` and `MatrixGame.toStrategicGame` | a generic interface proves transport once; bridges keep concrete, computable instances, and EconCSLib's design notes reject wrapper abstractions |

The outcome layer explains a pattern across all three surveys. Where outcomes exist, bridges and simulations can prove law equality and conclude for every preference, as `MixtureSimulation` does. Where they do not, as in EconCSLib's strategic games, payoffs are numbers from the start and every mixed concept is stated in an ordered field.

## Three libraries compared

The three libraries sit at different points of the same design space: MathEconLib stores the most structure in maps between problems, GameTheory in outcome laws and relations, and EconCSLib in concrete per-domain structures. All three over-bundle in the same direction, by stating Score-level facts in an ordered field or ℝ.

| Aspect | MathEconLib | GameTheory | EconCSLib |
| --- | --- | --- | --- |
| Core equilibrium object | `EquilibriumProblem`: deviation relation, values, validity | `IsEquilibrium`: a relation on outcome laws, a status quo, a deviation scheme | separate predicates per game type (`IsNashEquilibrium`, `IsMixedNashEq`, …) |
| Level as stored | Score shape with a lawless `LE` | Pairwise on laws | Score with `[Preorder U]`; ordered field or ℝ for mixed, coalitional and auction concepts |
| Level the core uses | Stay-vs-move | Stay-vs-move | Stay-vs-move for Nash; laws of `Preorder` unused |
| Outcome layer | yes in `Strategic/Outcome`, absent in `EquilibriumProblem` | yes, `PMF Outcome` | no; payoffs are numbers |
| Deviations | a relation | move types with an action on subprofiles | `Function.update`; a relation (`IVariant`) on trees |
| Maps and transport | morphisms, comorphisms, simulations, law simulations, value maps | scheme homomorphisms, language bridges (law equality) | bridge functions with a few transport theorems (tree to strategic at Stay-vs-move, matrix to strategic at Expected) |
| Invariance results | `mapValues`, affine invariance of expected values | vNM uniqueness up to positive affine | `IsBestResponse.congr_payoff` only |
| Representation theorems | ordinal, finite types; finite Afriat (#296) | vNM for finite outcomes; finite-menu choice (D84) | definitions and vNM axiom independence, no existence |
| Mixture laws | absent | `Preference.Convex`, vNM axioms | vNM axioms on `Lottery`, unconnected to games |
| Coalition moves | standalone predicates | "some member weakly prefers" aggregator | blocking pairs, sum inequalities, Pareto |
| Distinct strength | a family of transport certificates | Law-only bridges and Protocol semantics | breadth and computable instances |

### EconCSLib in more detail

EconCSLib's rule is that structures hold data, not assumptions (`docs/design.md`). `StrategicGame N U` stores `strategy` and `payoff : (∀ i, strategy i) → N → U` with no order (`GameTheory/StrategicGame/Basic.lean:33`), and order arrives at each definition. That is closest to MathEconLib's value-based design, with two differences: `[Preorder U]` instead of a lawless `LE`, and deviation fixed as `Function.update` instead of a relation. Its over-bundling is at the theorem level:

- `IsNashEquilibrium` (`NashEquilibrium.lean:28`) needs only `LE` but asks for `Preorder`.
- Potential-game and zero-sum theorems ask for an ordered field where an ordered additive group or a linear order suffices (`PotentialGame.lean:64`, `ZeroSum/Basic.lean:157`).
- The core, ESS and indivisible EF1/EFX are stated in ℝ where an ordered monoid or an order suffices.
- Three mixed-Nash predicates coexist, and only the matrix-game one is bridged to the strategic one (`MatrixGameNash.lean:619`).

Its tree layer is the one place it uses a deviation relation: `GameTree.toStrategicGame_nash_iff_isNashAt` (`GameTreeStrategicForm.lean:76`) matches `Function.update` deviations with `IVariant` deviations and needs no order laws, a Stay-vs-move transport of the kind `of_deviation_comparisons` generalizes. Its validity predicates are local (`feasible` fields, `IsFeasibleICIRIntegrable`), not a uniform Gate. The EconCSLib items come from one survey read and were not checked line by line.

## Design principles

Nine principles follow from the evidence; each names the finding it rests on. MathEconLib-specific options are on the Survey evidence tab, under Design options.

1. **State a result at the lowest level that passes the invariance test.** If the proof never inspects the values, the statement should not fix them. The morphism proofs use `value_eq` only to rewrite one comparison.
2. **Give a level its own structure only when a client needs an operation that hypotheses cannot supply.** In GameTheory's experiments no level met this bar (D92). `ComparisonMixture` has no library client.
3. **Keep order laws as hypotheses where several levels share one carrier.** GameTheory's `Ranking` does this; typeclasses fit only when one canonical order per type is intended.
4. **Keep an explicit outcome layer wherever "for every payoff" results are wanted.** `MixtureSimulation` exists because `Strategic/Outcome` has outcomes; EconCSLib's number-valued payoffs cannot express it.
5. **Keep the weak form, and assume comparability only where the weak and strict readings must agree.** Comparability at the incumbent and each replacement suffices (D79, D82); `isStrongNash_iff_not_lt` currently assumes a global `LinearOrder`.
6. **Make a Common scale an explicit parameter.** Efficiency, revenue and welfare statements need it; sharing one `V` across judges should not imply it.
7. **Pair every forgetful map with a verdict-preservation lemma, and every representation theorem with its uniqueness group.** GameTheory's vNM theorem and its positive-affine uniqueness (`Core/VNM.lean:207`) are the model; MathEconLib's affine iff is the matching invariance at the game level.
8. **Keep the Gate separate from judgment, and split it.** `valid` guards the incumbent, but the mixed and Bayesian problems put deviation integrability inside `deviation` (`isMixedNash_iff`, `bneProblem_deviation_iff`). Excluding non-integrable deviations differs from requiring every offered deviation to be integrable (D81, D92).
9. **Use bridges to supply certificates, and let one generic theorem consume them where that is shorter.** Exact lifts, domination, averaging bounds and law simulations can all feed `of_deviation_comparisons`; GameTheory found direct proofs slightly shorter for two bridges (D78), so the generic route need not be mandatory.

## Open questions

These are the points the evidence does not settle.

- **Do coalition moves need order-level certificates?** GameTheory's weak form with local comparability covered strong Nash and a matching case without a new structure (D82, D83). Whether domination or averaging should apply to coalition moves is open.
- **Which mixture law does each MathEconLib client need?** A single Mixable level was refuted (D80, D89). The averaging and law-simulation certificates should each state the closure they use; correlated equilibrium and mixed dominance have no MathEconLib client.
- **Does a separate Stay-vs-move structure pay off, given that a lawless `LE` already encodes it?** MathEconLib's explicit comparison relations (`IsOptimalWith`, #281) sit on the existing record without one, and GameTheory's guarded predicate needs none either (D81).
- **How does the invariance test handle mixed statements?** GameTheory's `IsεProper` bounds probabilities by ε while comparing values only ordinally, so it needs a group acting on two carriers at once.
- **Where should continuous (Debreu) representation live?** Finite revealed preference exists in MathEconLib (#296) and GameTheory (D84); MathEconLib's choice files remain the natural host for Debreu.
- **Do certificate conversions compose and commute with forgetful maps?** If they do, problems, maps and certificates form one categorical structure; this was not checked.
- **How should concepts outside the one-step scheme be organized?** ESS, limit refinements and iterated elimination each need a different kind of layer above the verdict.
