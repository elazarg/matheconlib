/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Algebra.Order.Module.Defs

/-! # Componentwise ordered scalar multiplication on products -/

@[expose] public section

namespace Prod

instance instIsOrderedModule {R M N : Type*} [Preorder R] [Zero R]
    [Preorder M] [Zero M] [Preorder N] [Zero N] [SMul R M] [SMul R N]
    [IsOrderedModule R M] [IsOrderedModule R N] : IsOrderedModule R (M × N) where

end Prod
