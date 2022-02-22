/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functoriality_additive
import algebraic_topology.dold_kan.equivalence_pseudoabelian

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents
open algebraic_topology

universes v
variables {C D : Type*} [category.{v} C] [category.{v} D]
  [additive_category C] [additive_category D]
  [is_idempotent_complete C] [is_idempotent_complete D]

variables (F : C ⥤ D) [functor.additive F]

namespace category_theory

namespace idempotents

namespace dold_kan

def functoriality_κinv' :
  (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse)
  ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) :=
begin
  calc (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse)
    ≅ 𝟭 _ ⋙ (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse) : by refl
  ... ≅ (κequiv'.inverse ⋙ κequiv'.functor) ⋙
      (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse) :
        iso_whisker_right κequiv'.counit_iso.symm _
  ... ≅ κequiv'.inverse ⋙ (κequiv'.functor ⋙
      preadditive.dold_kan.functor_karoubi_homological_complex_obj F) ⋙ κequiv'.inverse : by refl
  ... ≅ κequiv'.inverse ⋙ (functor.map_homological_complex F (complex_shape.down ℕ) ⋙ κequiv'.functor) ⋙ κequiv'.inverse :
    iso_whisker_left _ (iso_whisker_right (eq_to_iso (preadditive.dold_kan.functor_karoubi_homological_complex_compat F)) _)
  ... ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) ⋙ (κequiv'.functor ⋙ κequiv'.inverse) : by refl
  ... ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) ⋙ 𝟭 _ :
    iso_whisker_left _ κequiv'.unit_iso.symm
  ... ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) : functor.right_unitor _,
end

def functoriality_N : (simplicial_object.whiskering C D).obj F ⋙ N ≅
  N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :=
begin
  calc (simplicial_object.whiskering C D).obj F ⋙ N
    ≅ (dold_kan.N' ⋙ preadditive.dold_kan.functor_karoubi_homological_complex_obj F) ⋙ κequiv'.inverse :
      iso_whisker_right (eq_to_iso (preadditive.dold_kan.functoriality_N' F)) _
  ... ≅ dold_kan.N' ⋙ (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse) : by refl
  ... ≅ dold_kan.N' ⋙ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) :
    iso_whisker_left _ (functoriality_κinv' F)
  ... ≅ N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) : by refl,
end

end dold_kan

end idempotents

end category_theory
