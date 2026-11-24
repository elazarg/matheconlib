# Comments on [matheconlib/matheconlib#277](https://github.com/matheconlib/matheconlib/issues/277): population games

_This note was drafted with Claude Code from a discussion comparing that issue with abstraction experiments I ran in my GameTheory and matheconlib forks. The points are ordered from most to least confident, and links are pinned to commits._

## 1. Mass caps don't need a more general `EquilibriumProblem`, but they do change the characterizations

On Bolton's second comment: `EquilibriumProblem` can already express state-dependent restrictions. In `choiceProblem`, the aggregate `x` is a fixed parameter, and `deviation` may depend on it, e.g. `deviation _ _ b := x.val i b < cap i b`. The limitation is that `PopulationGame` has nowhere to carry the restriction, and `choiceProblem` fixes `deviation _ _ _ := True`.

Caps do break the best-response form of deliverable 2. Take one population of mass 1 and two actions with constant payoffs `u_a = 0` and `u_b = 1`, and cap `b` at `1/2`:

- `x = (1/2, 1/2)` is an equilibrium of the capped game, since no one may move to `b`.
- It fails `∀ a b, 0 < x.val i a → G.payoff x i b ≤ G.payoff x i a`, since the occupied action `a` pays less than `b`.
- The variational inequality still holds over the capped feasible states: `∑ₐ (y a − x a) · u_a = (y_b − 1/2) · 1 ≤ 0`.

So if restrictions are added later, deliverables 2 and 3 should state the unrestricted case as an explicit hypothesis.

One trap to avoid: adding the cap to `IsFeasible` while keeping every deviation admissible. In the example, every capped state then has `a` occupied while `b` pays more, so the capped game has no equilibrium at all. Filtering states by feasibility can't replace restricting deviations. I hit the same distinction in a shared-capacity game in GameTheory: [D87, "Native shared-capacity discriminator"](https://github.com/elazarg/GameTheory/blob/7608763f711c5f60ac66186d7282d16bb1dc2394/docs/decisions/D87-simultaneous-feasible-choice.md#native-shared-capacity-discriminator).

Two related results, which are analogues rather than population games:

- **Restricted menus** ([MEC-016](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/docs/experiments/EconomicBuildingBlocksLog.md#mec-016-admissibility-of-extracted-pure-witnesses)). Under a mean budget, an incumbent rejects every admitted pure deviation ([`all_admitted_pure_rejected`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/RestrictedMixedMenu.lean#L56)) yet loses to an admitted mixture ([`incumbent_not_equilibrium`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/RestrictedMixedMenu.lean#L72)). The mixture's improving component is exactly the one the budget excludes ([`mean_budget_not_support_hereditary`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/RestrictedMixedMenu.lean#L78)). Checking pure deviations suffices once the menu is closed under taking supported components ([`pure_deviations_suffice_of_support_hereditary`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/RestrictedMixedMenu.lean#L112)). Here, the converse direction of point 3 needs the comparator "move `a`'s mass to `b`" to be admissible. That always holds without caps and can fail with them.
- **Action domains** ([MEC-015](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/docs/experiments/EconomicBuildingBlocksLog.md#mec-015-action-domains-at-positive-marginal-cost)). With the same mechanism, transfers and prior, restricting bids to be nonnegative turns a non-equilibrium ([`zeroReal_not_isBNE`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/Mechanism/AllPurchaseActionDomain.lean#L120)) into an equilibrium ([`zeroRestricted_isBNE`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/Mechanism/AllPurchaseActionDomain.lean#L148)).

The safe direction is already on main: an unrestricted equilibrium remains one under any restriction ([`IsEquilibrium.of_deviation_subset`](https://github.com/matheconlib/matheconlib/blob/ad8b79a9c11a3dd3d4a23f1d74c0bad2285ba89b/MathEconLib/GameTheory/Equilibrium/Problem.lean#L169)).

## 2. `choiceProblem` needs a `valid` field

Since [#252](https://github.com/matheconlib/matheconlib/issues/252), `EquilibriumProblem` has a [`valid`](https://github.com/matheconlib/matheconlib/blob/ad8b79a9c11a3dd3d4a23f1d74c0bad2285ba89b/MathEconLib/GameTheory/Equilibrium/Problem.lean#L79) field. The sketch here, and the version in [#274](https://github.com/matheconlib/matheconlib/issues/274), predate it, so they no longer build on main. `valid _ := True` is the minimal fix.

An option, with lower confidence: `valid a := 0 < x.val i a` puts the occupancy guard inside the choice problem. Then `IsSubpopulationEquilibrium x i` reads "every valid action is an equilibrium", and anything stated generically over `EquilibriumProblem` sees the guard. Validity carries information that deviation optimality can't. With no deviators, an invalid incumbent is vacuously optimal but still not an equilibrium ([`noJudges`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/CandidateValidity.lean#L56), [`noJudges_not_equilibrium`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/CandidateValidity.lean#L63)). The same holds with no admitted deviations ([`invalid_isDeviationOptimal`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/CandidateValidity.lean#L72)). I don't yet have a theorem this option unlocks, so either choice seems fine to me.

## 3. The variational inequality is an expectation bound

Fix a population `i` with mass `m > 0` and a feasible comparator `y`. Then `y_i / m` is a `FinDist (A i)`, so `∑ₐ y_i a · u_a = m · E[u] ≤ m · max u`. When every occupied action is a maximizer, `m · max u = ∑ₐ x_i a · u_a`. Zero mass is trivial.

With deliverable 1's identification with `FinDist`, the forward direction should be short using [`FinDist.expect_mono`](https://github.com/matheconlib/matheconlib/blob/ad8b79a9c11a3dd3d4a23f1d74c0bad2285ba89b/MathEconLib/Probability/FinDist/Expect.lean#L116) and [`FinDist.expect_const`](https://github.com/matheconlib/matheconlib/blob/ad8b79a9c11a3dd3d4a23f1d74c0bad2285ba89b/MathEconLib/Probability/FinDist/Expect.lean#L70), both on main. For the converse, take `y` to move all of `a`'s mass to `b`. Strategic games use the same "a mixture is worth at most its best pure action" step, so the two could share a lemma.

## 4. On `NNReal` versus `ℝ`

One more point in favor of `ℝ`: the acceptance criterion "negative allocations fail feasibility" can't be stated with `NNReal`, since the type rules them out. `ℝ` also matches `FinDist` directly.

## 5. The occupancy guard won't extend to infinitely many actions

"Every occupied action is a best response" relies on finitely many actions, so that occupied means positive mass on an atom. With a continuum of actions, a state can put zero mass on every single action, and the condition becomes vacuous. I have a compiled instance of this in a mixed outcome game ([MEC-017](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/docs/experiments/EconomicBuildingBlocksLog.md#mec-017-atomic-and-nonatomic-mixture-provenance)):

- Every action singleton has mass zero ([`action_singleton_zero`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/NonatomicWitnessBoundary.lean#L39)).
- The outcome is nevertheless certain success.
- No positive-mass action can witness it ([`no_positive_atom_witness`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/NonatomicWitnessBoundary.lean#L80), [`success_without_positive_atom`](https://github.com/elazarg/matheconlib/blob/26e086f9dd766bea2f31b4a8c4fd878d5088bfbc/MathEconLibTest/GameTheory/NonatomicWitnessBoundary.lean#L87)).

The deferred infinite-action follow-up will need a support or almost-everywhere formulation rather than `0 < x.val i a`.

## 6. Existence (deferred) has a ready-made route — not yet compiled

By the variational form, a population equilibrium is a state where each population's allocation maximizes `y ↦ ∑ₐ y a · payoff x i a` over its feasible allocations, with `x` held fixed. That has the shape of [`exists_feasibleChoice_fixedPoint`](https://github.com/elazarg/GameTheory/blob/8aab006efb7d7242bf1920856443fdfca25f1f43/GameTheory/Analysis/FeasibleChoiceFixedPoint.lean#L27) in GameTheory:

- **Coordinates:** finitely many populations.
- **Menus:** mass-scaled simplices. They are compact and convex, and nonempty unless a positive-mass population has no actions, which matches the boundary case in the acceptance criteria. The theorem also allows menus that depend on the state, so caps fit.
- **Scores:** linear, hence quasiconcave, in the alternative.
- **Extra hypothesis:** payoffs continuous in the state.

I haven't compiled this instantiation, and using it would raise the question of where shared parametric-optimality mathematics should live.

## 7. Price of anarchy — an observation, no action needed

GameTheory proves the atomic affine `5/2` bound through a smoothness theorem ([`IsSmooth.nash_bound`](https://github.com/elazarg/GameTheory/blob/8aab006efb7d7242bf1920856443fdfca25f1f43/GameTheory/Core/Welfare.lean#L110), applied in [`AffinePoA.lean`](https://github.com/elazarg/GameTheory/blob/8aab006efb7d7242bf1920856443fdfca25f1f43/GameTheory/Congestion/AffinePoA.lean#L186)). [#274](https://github.com/matheconlib/matheconlib/issues/274)'s Pigou-bound step `(1 − β) · C(f) ≤ C(g)` is the nonatomic version of the same argument. The theorems differ, but if PoA results keep accumulating, the smoothness statement is the natural shared form.
