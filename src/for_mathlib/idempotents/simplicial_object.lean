/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_object
import for_mathlib.idempotents.functor_categories

namespace category_theory

namespace idempotents

variables {C : Type*} [category C] [is_idempotent_complete C]

instance : is_idempotent_complete (simplicial_object C) := idempotents.functor_category_is_idempotent_complete
instance : is_idempotent_complete (cosimplicial_object C) := idempotents.functor_category_is_idempotent_complete

end idempotents

end category_theory