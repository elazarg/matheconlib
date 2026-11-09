/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Module.Prod

/-! # Componentwise ordered scalar multiplication on products -/

@[expose] public section

namespace Prod

instance instIsOrderedModule {R M N : Type*} [Preorder R] [Zero R]
    [Preorder M] [Zero M] [Preorder N] [Zero N] [SMul R M] [SMul R N]
    [IsOrderedModule R M] [IsOrderedModule R N] : IsOrderedModule R (M × N) where
  smul_le_smul_of_nonneg_left := by
    intro a ha b c h
    exact ⟨smul_le_smul_of_nonneg_left h.1 ha, smul_le_smul_of_nonneg_left h.2 ha⟩
  smul_le_smul_of_nonneg_right := by
    intro b hb a c h
    exact ⟨smul_le_smul_of_nonneg_right h hb.1, smul_le_smul_of_nonneg_right h hb.2⟩

end Prod
