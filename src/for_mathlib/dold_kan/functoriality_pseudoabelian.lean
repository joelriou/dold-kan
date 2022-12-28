/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.functoriality_additive
import for_mathlib.dold_kan.equivalence_pseudoabelian

/-!

# Functoriality of the Dold-Kan correspondence for pseudoabelian categories

-/

noncomputable theory

open category_theory
open category_theory.idempotents
open category_theory.limits
open algebraic_topology

variables {C D : Type*} [category C] [category D]
  [preadditive C] [preadditive D] [has_finite_coproducts C] [has_finite_coproducts D]
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
  F.map_karoubi_homological_complex _ ⋙ (to_karoubi_equivalence (chain_complex _ ℕ)).inverse
  ≅ (to_karoubi_equivalence _).inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ) :=
begin
  calc (F.map_karoubi_homological_complex _ ⋙ (to_karoubi_equivalence (chain_complex _ ℕ)).inverse)
    ≅ 𝟭 _ ⋙ (F.map_karoubi_homological_complex _ ⋙ (to_karoubi_equivalence _).inverse) :
          by refl
  ... ≅ ((to_karoubi_equivalence _).inverse ⋙ (to_karoubi_equivalence _).functor) ⋙
      (F.map_karoubi_homological_complex _ ⋙ (to_karoubi_equivalence _).inverse) :
        iso_whisker_right (to_karoubi_equivalence _).counit_iso.symm _
  ... ≅ (to_karoubi_equivalence _).inverse ⋙ ((to_karoubi_equivalence _).functor ⋙
      F.map_karoubi_homological_complex _) ⋙ (to_karoubi_equivalence _).inverse : by refl
  ... ≅ (to_karoubi_equivalence _).inverse ⋙
    (functor.map_homological_complex F (complex_shape.down ℕ) ⋙ (to_karoubi_equivalence _).functor) ⋙
    (to_karoubi_equivalence _).inverse : iso_whisker_left _ (iso_whisker_right
        (eq_to_iso (F.map_homological_complex_karoubi_compatibility _)) _)
  ... ≅ ((to_karoubi_equivalence _).inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) ⋙
    ((to_karoubi_equivalence _).functor ⋙ (to_karoubi_equivalence _).inverse) : by refl
  ... ≅ ((to_karoubi_equivalence _).inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) ⋙ 𝟭 _ :
    iso_whisker_left _ (to_karoubi_equivalence _).unit_iso.symm
  ... ≅ ((to_karoubi_equivalence _).inverse ⋙ functor.map_homological_complex F (complex_shape.down ℕ)) :
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
    ≅ (dold_kan.N₁ ⋙ F.map_karoubi_homological_complex _) ⋙
      (to_karoubi_equivalence _).inverse : iso_whisker_right (eq_to_iso (preadditive.dold_kan.functoriality_N₁ F)) _
  ... ≅ dold_kan.N₁ ⋙ (F.map_karoubi_homological_complex _ ⋙
        (to_karoubi_equivalence _).inverse) : by refl
  ... ≅ dold_kan.N₁ ⋙ ((to_karoubi_equivalence _).inverse ⋙
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
