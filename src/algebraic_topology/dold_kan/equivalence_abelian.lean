/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_pseudoabelian

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

variables {C : Type*} [category C] [additive_category C]

namespace category_theory

namespace abelian

namespace dold_kan

open algebraic_topology.dold_kan

--@[simps]
def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
sorry

end dold_kan

end abelian
#check

end category_theory