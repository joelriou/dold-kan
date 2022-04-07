/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.functoriality_pseudoabelian
import algebraic_topology.dold_kan.equivalence

/-!

# Functoriality of the Dold-Kan correspondence for abelian categories

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents
open algebraic_topology

variables {A : Type*} [category A] [abelian A]
variables {B : Type*} [category B] [abelian B]

namespace category_theory

namespace abelian

namespace dold_kan

/-- Given an additive functor `F : A ⥤ B` between abelian categories,
this is the functoriality isomorphism between the two functors
`simplicial_object A ⥤ chain_complex B ℕ` obtained by
using the functors induced by `F` and the functor `N` in `A` or in `B`. -/
@[simps]
def functoriality_N (F : A ⥤ B) [functor.additive F]:
  (simplicial_object.whiskering A B).obj F ⋙ N ≅
  N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :=
begin
  calc (simplicial_object.whiskering A B).obj F ⋙ N
    ≅ (simplicial_object.whiskering A B).obj F ⋙ idempotents.dold_kan.N :
      iso_whisker_left _ comparison_N
  ... ≅ idempotents.dold_kan.N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :
    idempotents.dold_kan.functoriality_N F
  ... ≅ N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :
    iso_whisker_right comparison_N.symm _,
end

/- TODO: Compare this isomorphism with the mostly obvious natural transformation that
can be constructed from the original definition of the normalized Moore complex using kernels.

lemma compatibility_N_degreewise (F : A ⥤ B) [functor.additive F]
  (X : simplicial_object A) :
  ((functoriality_N F).inv.app X) ≫
    ((inclusion_of_Moore_complex B).app (((simplicial_object.whiskering A B).obj F).obj X)) =
    (functor.map_homological_complex F (complex_shape.down ℕ)).map
      ((inclusion_of_Moore_complex A).app X) ≫
    eq_to_hom (congr_obj (map_alternating_face_map_complex F) X) := sorry
-/

end dold_kan

end abelian

end category_theory
