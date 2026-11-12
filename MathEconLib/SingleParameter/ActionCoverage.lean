/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.SingleParameter.IC

/-!
# Extending report incentives through payoff coverage

An original action can be rejected using report incentives when a report
payoff-dominates it at the same true type. Feasibility of the prescribed
strategy remains an explicit, separate condition.
-/

@[expose] public section

namespace MathEconLib.SingleParameterProblem


/-- Report IC extends to feasible actions through payoff domination by reports. -/
theorem HasTypeDeviationIC.hasUniversalIC_of_payoff_coverage {Action : Type*}
    {P : SingleParameterProblem Action} (typeIC : HasTypeDeviationIC P)
    {feasible : Set Action}
    (strategyFeasible : ∀ v ∈ P.typeInterval, P.strategy v ∈ feasible)
    (coverage : ∀ v ∈ P.typeInterval, ∀ action ∈ feasible,
      ∃ report ∈ P.typeInterval, P.payoff v action ≤ P.payoff v (P.strategy report)) :
    HasUniversalIC P feasible where
  strategyInS := strategyFeasible
  universalIC v valid action admitted := by
    obtain ⟨report, validReport, bound⟩ := coverage v valid action admitted
    exact bound.trans (typeIC.typeDeviationIC v valid report validReport)

end MathEconLib.SingleParameterProblem
