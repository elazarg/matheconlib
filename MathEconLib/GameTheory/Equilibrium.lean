/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.GameTheory.Equilibrium.Mixture

/-!
# Equilibrium problems and transport

Every certificate below transports `EquilibriumProblem.IsEquilibrium`; prove the cheapest one
that holds, and convert it when a more general transport theorem is needed.

* One incumbent, no reuse: `EquilibriumProblem.IsEquilibrium.of_deviation_comparisons` needs only
  a matching of comparisons, and is equivalent to per-deviator transport.
* Exact correspondence of deviations and values: `GameMorphism` (transport) or `GameComorphism`
  (reflection).
* Each target deviation bounded by one source deviation after monotone recoding: `GameSimulation`,
  which composes. Additive errors chain one step at a time.
* Each target deviation bounded by a mean of source deviations, with ordered vector values:
  `EquilibriumProblem.IsEquilibrium.of_integral_bounds`. For real values this yields a
  `GameSimulation` by `GameSimulation.ofIntegralBounds`.
* Each target deviation's outcome law a mixture of legal source laws, independent of utility:
  `MixtureSimulation`, which transports every integrable ordered evaluation and composes when
  source deviation sets are measurable.
-/
