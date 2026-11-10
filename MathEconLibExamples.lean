/-
Copyright (c) 2026 Daniel Lyng, Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, Elazar Gershuni
-/
module

public import MathEconLibExamples.GameTheory.DominatedStrategies
public import MathEconLibExamples.GameTheory.MatchingPennies
public import MathEconLibExamples.Preferences.Finite
public import MathEconLibExamples.SingleParameter.BeckerCrime

/-!
# Mathematical economics examples

Concrete economic models illustrate the library's definitions and results.

## Main statements

* Matching pennies has a unique mixed Nash equilibrium: Both players randomize uniformly.
* Matching pennies has no pure Nash equilibrium.
* A mixed-strategy dominance reduction preserves Nash despite having no exact payoff lift.
* A Becker-inspired crime-choice model gives a threshold rule and deterrence results
  for individuals and aggregate crime under a fixed type distribution.

## Tags

mathematical economics, examples, game theory, nash equilibrium, price theory
-/
