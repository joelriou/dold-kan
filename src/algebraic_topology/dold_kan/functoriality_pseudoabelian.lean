/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functoriality_additive
import algebraic_topology.dold_kan.equivalence_pseudoabelian

/-!

# Functoriality of the Dold-Kan correspondance for pseudoabelian categories

-/

noncomputable theory

open category_theory
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

/-- Functoriality property of the inverse functor
  `κequiv'.inverse : karoubi (chain_complex C ℕ) ⥤ chain_complex C ℕ` for two categories
  `C` and `D` and a functor `F : C ⥤ D`. This is deduced by the similar equality of
  functors `preadditive.dold_kan.functor_karoubi_homological_complex_compat` for the
  functors `κequiv'.functor`. -/
def functoriality_κinv' :
  (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse)
  ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) :=
begin
  calc (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse)
    ≅ 𝟭 _ ⋙ (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse) :
          by refl
  ... ≅ (κequiv'.inverse ⋙ κequiv'.functor) ⋙
      (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙ κequiv'.inverse) :
        iso_whisker_right κequiv'.counit_iso.symm _
  ... ≅ κequiv'.inverse ⋙ (κequiv'.functor ⋙
      preadditive.dold_kan.functor_karoubi_homological_complex_obj F) ⋙ κequiv'.inverse : by refl
  ... ≅ κequiv'.inverse ⋙
    (functor.map_homological_complex F (complex_shape.down ℕ) ⋙ κequiv'.functor) ⋙
    κequiv'.inverse : iso_whisker_left _ (iso_whisker_right
        (eq_to_iso (preadditive.dold_kan.functor_karoubi_homological_complex_compat F)) _)
  ... ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) ⋙
    (κequiv'.functor ⋙ κequiv'.inverse) : by refl
  ... ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) ⋙ 𝟭 _ :
    iso_whisker_left _ κequiv'.unit_iso.symm
  ... ≅ (κequiv'.inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) :
    functor.right_unitor _,
end

/-- Given an additive functor `F : A ⥤ B` between pseudoabelian categories,
this is the functoriality isomorphism between the two functors
`simplicial_object A ⥤ chain_complex B ℕ` obtained by using the functors
induced by `F` and the functor `N` in `A` or in `B`. -/
def functoriality_N : (simplicial_object.whiskering C D).obj F ⋙ N ≅
  N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :=
begin
  calc (simplicial_object.whiskering C D).obj F ⋙ N
    ≅ (dold_kan.N₁ ⋙ preadditive.dold_kan.functor_karoubi_homological_complex_obj F) ⋙
      κequiv'.inverse : iso_whisker_right (eq_to_iso (preadditive.dold_kan.functoriality_N₁ F)) _
  ... ≅ dold_kan.N₁ ⋙ (preadditive.dold_kan.functor_karoubi_homological_complex_obj F ⋙
        κequiv'.inverse) : by refl
  ... ≅ dold_kan.N₁ ⋙ (κequiv'.inverse ⋙
    functor.map_homological_complex F (complex_shape.down ℕ)) :
        iso_whisker_left _ (functoriality_κinv' F)
  ... ≅ N ⋙ functor.map_homological_complex F (complex_shape.down ℕ) : by refl,
end

/- TODO : show that `functoriality_N (𝟭 C)` is `iso.refl _`, and that `functoriality_N`
satisfies a transitivity property when composing two functors `C ⥤ D` and `D ⥤ E`.
Note that in the additive case, `preadditive.dold_kan.functoriality_N` was an *equality*
of functors, so that associated `eq_to_iso _` isomorphisms automatically satisfy
the transitivity property. -/

end dold_kan

end idempotents

end category_theory
