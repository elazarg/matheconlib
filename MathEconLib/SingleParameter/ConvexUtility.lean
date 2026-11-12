/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import MathEconLib.SingleParameter.IC
public import MathEconLib.ForMathlib.SupportingSlopes.Convexity

/-!
# Convex indirect utility from report incentive compatibility

The supporting-slope condition implies convex utility on the type interval.
This conclusion uses neither the allocation bound nor analytic regularity.
-/

@[expose] public section

namespace MathEconLib.SingleParameterProblem

/-- Report incentive compatibility gives convex indirect utility. -/
theorem U_convexOn {Action : Type*} (P : SingleParameterProblem Action) [HasEnvelopeIC P] :
    ConvexOn ℝ P.typeInterval P.U :=
  SupportingSlopesOn.convexOn (HasEnvelopeIC.envelopeIC (P := P)) (convex_Icc _ _)

end MathEconLib.SingleParameterProblem
