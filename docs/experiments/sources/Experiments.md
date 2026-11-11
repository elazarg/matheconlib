# Experiments for MathEconLib

Six small Lean experiments, each designed so that either outcome counts as evidence. The question is whether MathEconLib's `EquilibriumProblem` should also be its internal building block, or only the vocabulary clients use.

## The question

Two hypotheses make different predictions:

- **Vocabulary only.** `EquilibriumProblem` and its maps are a good client-facing language for games. Internally, results are better built from small Mathlib-level operations (guarded optimality, coverage, choice) that mechanism design, matching and choice can share. This predicts cross-area reuse of those operations, and plumbing when a proof is routed through the record.
- **Building block.** The record and its maps are also the right internal layer. This predicts that proofs routed through a map are shorter than direct ones, and that one map serves several statements.

The experiments below are chosen so that each outcome counts for one side. If E1 favours the record and E3 finds no cross-area reuse, the vocabulary-only hypothesis is wrong for MathEconLib.

## Where the record is used

On upstream main (`b0c6f35`), the record is the strategic-game layer's representation; the rest of the library keeps its own predicates and connects through bridges.

- **Defined through the record:** `IsNash`, `IsMixedNash`, `IsFiniteMixedNash` (through `IsNash` of the finite extension), `IsBNE`, `IsBNEFin`. Cournot reaches it through `comapActions`.
- **Standalone:** `IsStrictNash`, `IsStrongNash`, `IsDSIC`, `IsBICOn`, `IsStableMatching`, `IsEfficient` (an `IsMaxOn`). Mechanism concepts reach the record only through the bridges `IsDSIC.isNash` and `IsBIC.isBNE`. The single-parameter `revelation_principle` is an existential over a reduced problem and uses neither the record nor its maps.
- **Three unconnected optimality notions:** `IsDeviationOptimal` and `IsOptimalWith` (rooted comparison, no order laws, no menu membership); `Choice.maximizers` (`IsGreatest` under a bundled `Preference`: membership plus a preorder); `IsMaxOn` (a score, no membership). The `GameTheory` modules do not import `Choice`.
- **Integrability:** the mixed and Bayesian problems put deviation integrability inside `deviation` (`isMixedNash_iff`, `bneProblem_deviation_iff`), and `valid` guards only the incumbent. `MathEconLibTest/GameTheory/Integrability.lean` covers a non-integrable incumbent, not a non-integrable deviation.

## The experiments

| # | Experiment | Deliverable | Counts for building blocks if | Counts for the record if | Size (lines) |
| --- | --- | --- | --- | --- | --- |
| E1 | Bayesian revelation principle through a map | a BNE of an indirect mechanism gives a truthful BNE of the composed direct mechanism, proved both through a `GameMorphism` and directly | the map route needs plumbing the direct proof avoids, or the map has no second use | the map route is shorter and the same map serves a second statement | 80–150 |
| E2 | Deviation with infinite gain | a two-player game where `IsMixedNash` holds although one deviation has expected payoff +∞ | mixed and Bayesian certificates shrink once deviation evaluability is a separate guard | filtering is the intended convention and no certificate shrinks | 40–60 |
| E3 | One optimality predicate | a Mathlib-only guarded predicate, three definitional specializations, one coverage lemma used in two areas | theorems in two areas become corollaries with no added hypotheses | the specializations need coercions or extra hypotheses, or no non-game theorem uses the lemma | 60 plus rewrites |
| E4 | Strong Nash without a linear order | `isStrongNash_iff_not_lt` under local comparability, with a vector-payoff example | neither: it tests the invariance principle, not the record | neither | about 25 |
| E5 | Chained reductions | two rounds of dominated-action elimination, through composed `GameSimulation` records and through per-round hypotheses | the hypothesis route is as short | composition is shorter and extends to n rounds by induction | 60–120 |
| E6 | Mixed equilibrium over outcome laws | mixed Nash for a relation on outcome laws, expected value as one instance, an example that is not expected utility | a standard result holds for the example with only a mixture-closure hypothesis | the generalization still needs the record's value carrier | 200 or more |

## Details

### E1: Bayesian revelation principle through a map

MathEconLib has `IsBIC.isBNE` but no revelation principle for indirect Bayesian mechanisms, and `inducedBayesianGame` exists for any `Mechanism I A O`. Composing `M` with a measurable strategy profile `s` gives a direct mechanism. Each misreport strategy there lifts to an indirect strategy with the same ex-ante payoff, which is exactly a `GameMorphism`. Names are illustrative:

```lean
theorem isBNE_truthful_of_isBNE (M : Mechanism I A O)
    (s : (M.inducedBayesianGame E).Strategy)
    (h : (M.inducedBayesianGame E).IsBNE μ s) :
    ((M.compose s).inducedBayesianGame E).IsBNE μ
      (truthfulStrategy E (M.compose s))
```

Because `deviation` contains integrability, the map must carry integrability witnesses; that cost is part of the measurement. The natural second use is the dominant-strategy version through `utilityGame`.

### E2: Deviation with infinite gain

Player 0 picks a `Bool` and player 1 picks `n : ℕ`; player 1's payoff is 0. Player 0 earns 2^(n+1) for `true` and 0 for `false`. In `σ`, player 0 plays `false` and player 1 plays `n` with probability 2^−(n+1).

```lean
example : G.IsMixedNash σ        -- the deviation is filtered
example : ¬ Integrable (G.payoff 0)
    (lawOf (Function.update σ 0 (dirac true)))
-- that deviation's expected payoff is +∞
```

Under the current definition, player 0 is in equilibrium while a deviation pays +∞. The measurement is how many lines of `Bayesian/Measurable/Comap.lean` (125 lines, 9 mentioning integrability) and of the averaging and mixture certificates go to deviation integrability, before and after separating the guard. This bears on #242.

### E3: One optimality predicate

```lean
def IsOptimalOn (ok : α → Prop) (R : α → α → Prop)
    (S : Set α) (x : α) : Prop :=
  ok x ∧ ∀ y ∈ S, ok y ∧ R y x
```

Requiring every alternative to be evaluable is the predicate itself; filtering is `IsOptimalOn ok R {y ∈ S | ok y} x`. `IsDeviationOptimal` (per judge), `Choice.maximizers` (membership plus the predicate) and `IsMaxOn` should be definitional specializations. One coverage lemma, "if each target alternative is covered by a source alternative whose comparison implies the target's, optimality transfers", should then prove `GameMorphism.transport` and one `Choice` or `ValueDistribution` lemma.

### E4: Strong Nash without a linear order

```lean
lemma isStrongNash_iff_not_lt_of_comparable [Preorder V]
    (hc : ∀ a' ≠ a, ∀ i, a i ≠ a' i →
      G.payoff i a' ≤ G.payoff i a ∨
        G.payoff i a ≤ G.payoff i a') :
    G.IsStrongNash a ↔ ∀ a' ≠ a,
      ¬ ∀ i, a i ≠ a' i → G.payoff i a < G.payoff i a'
```

The existing `isStrongNash_iff_not_lt` (global `LinearOrder`) becomes a corollary, and an example with componentwise-ordered `ℝ × ℝ` payoffs uses the new form. GameTheory's analogue is `isStrongNash_iff_not_all_gain_of_comparable`.

### E5: Chained reductions

This uses branch `design/equilibrium-simulations` (`Strategic/Reduction.lean`). Route A composes two `dominatedActionSimulation` certificates. Route B applies `isNash_comapActions_iff_of_dominated` twice with explicit hypotheses. The result decides whether transport certificates need records with composition.

### E6: Mixed equilibrium over outcome laws

This builds on `Strategic/Outcome`. The comparison is a relation on outcome laws that keeps an upper bound under the deviation kernels actually used; two-way mixing closure is not enough (GameTheory's countable-mixture counterexample). A suitable example is GameTheory's possibility preference, which provably has no expected-utility representation. It is the most expensive experiment.

## Protocol

- Pin upstream main `b0c6f35`; E5 also uses branch head `13f5a84`.
- Fix the criteria in the table before writing code.
- Put each experiment in its own file in a scratch namespace and build it with `lake build <Module>`; no `sorry`, no `native_decide`.
- Report for each: the statement, nonblank lines per route, hypotheses added or removed, the build result and a one-paragraph verdict.
- Keep each deliverable under about 150 lines, so a maintainer can read it in one sitting.
- Run E4 and E2 first (small and self-contained), then E1 and E3 (they decide the question), then E5, and E6 only if the question is still open.
