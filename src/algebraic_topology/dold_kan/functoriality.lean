/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functoriality_pseudoabelian
import algebraic_topology.dold_kan.equivalence

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents
open algebraic_topology

universes v
variables {A : Type*} [category.{v} A] [abelian A]
variables {B : Type*} [category.{v} B] [abelian B]

variables (F : A ⥤ B) [functor.additive F]

namespace category_theory

namespace abelian

namespace dold_kan

@[simps]
def functoriality_N : (simplicial_object.whiskering A B).obj F ⋙ N ≅
  N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :=
begin
  calc (simplicial_object.whiskering A B).obj F ⋙ N
    ≅ (simplicial_object.whiskering A B).obj F ⋙ idempotents.dold_kan.N : iso_whisker_left _ comparison_N
  ... ≅ idempotents.dold_kan.N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :
    idempotents.dold_kan.functoriality_N F
  ... ≅ N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) : iso_whisker_right comparison_N.symm _,
end

/- TODO: In each degree, compare this isomorphism with the mostly obvious natural transformation that
can be constructed from the original definition of the normalized Moore complex using kernels. 

lemma compatibility_N_degreewise (X : simplicial_object A) (n : ℕ) :
  ((functoriality_N F).inv.app X).f n ≫
    ((inclusion_of_Moore_complex B).app (((simplicial_object.whiskering A B).obj F).obj X)).f n = 
    F.map (((inclusion_of_Moore_complex A).app X).f n) := sorry

-/

end dold_kan

end abelian

end category_theory