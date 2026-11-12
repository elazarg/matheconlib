/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
# Supporting slopes on a set

The affine line with value `U y` and slope `q y` supports `U` from below
at each point of the given set. This condition does not bound slopes, require
continuity, or choose a representation of the points as actions or reports.
-/

@[expose] public section

namespace MathEconLib

/-- Each assigned slope gives a global affine lower support on the specified set. -/
def SupportingSlopesOn (U q : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, (x - y) * q y ≤ U x - U y

namespace SupportingSlopesOn

/-- The canonical payment `y * q y - U y` makes every offered report weakly
less attractive than the utility assigned to the true point. -/
theorem report_payoff_le {U q : ℝ → ℝ} {S : Set ℝ} (h : SupportingSlopesOn U q S)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    x * q y - (y * q y - U y) ≤ U x := by
  have support := h x hx y hy
  nlinarith

/-- Supporting slopes are monotone even without bounds or continuity. -/
theorem monotoneOn {U q : ℝ → ℝ} {S : Set ℝ} (h : SupportingSlopesOn U q S) :
    MonotoneOn q S := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with equal | strict
  · exact equal ▸ le_refl _
  · by_contra! contrary
    have lower := h x hx y hy
    have upper := h y hy x hx
    nlinarith [mul_pos (sub_pos.mpr strict) (sub_pos.mpr contrary)]

end SupportingSlopesOn

end MathEconLib
