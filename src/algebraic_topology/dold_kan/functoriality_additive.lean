/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_additive

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents
open algebraic_topology

universe v
variables {C : Type*} [category.{v} C] [additive_category C]
variables {D : Type*} [category.{v} D] [additive_category D]
variables (F : C ⥤ D) [functor.additive F]

open algebraic_topology.dold_kan

namespace category_theory

namespace preadditive

namespace dold_kan

@[simps]
def functor_karoubi_simplicial_object :=
(simplicial_object.whiskering C D) ⋙ (functor_extension'' _ _)

@[simps]
def functor_karoubi_homological_complex_obj :
  karoubi (chain_complex C ℕ) ⥤ karoubi (chain_complex D ℕ) :=
(functor_extension'' _ _).obj (functor.map_homological_complex F (complex_shape.down ℕ))

lemma functor_karoubi_homological_complex_compat :
  to_karoubi _ ⋙ functor_karoubi_homological_complex_obj F =
  functor.map_homological_complex F (complex_shape.down ℕ) ⋙ to_karoubi _ :=
begin
  apply functor.ext,
  { intros X Y f,
    ext n,
    dsimp [to_karoubi],
    simp only [homological_complex.comp_f, karoubi.comp, karoubi.eq_to_hom_f,
      homological_complex.eq_to_hom_f, functor_karoubi_homological_complex_obj_obj_p_f,
      functor.map_homological_complex_map_f],
    erw [id_comp, comp_id, F.map_id, id_comp, comp_id], },
  { intro X,
    ext1,
    { erw [id_comp, comp_id],
      dsimp,
      ext n,
      simp only [functor_karoubi_homological_complex_obj_obj_p_f, to_karoubi_obj_p],
      erw [homological_complex.id_f, F.map_id],
      refl, },
    { refl, }, },
end

lemma functor_extension'_comp (C D E : Type*) [category C] [category D] [category E]
  (F : C ⥤ karoubi D) (G : D ⥤ karoubi E) :
  (functor_extension' C E).obj (F ⋙ (functor_extension' D E).obj G) =
  (functor_extension' C D).obj F ⋙ (functor_extension' D E).obj G :=
begin
  apply functor.ext,
  { intros X Y f,
    erw [id_comp, comp_id],
    refl, },
  { intro P,
    ext,
    { dsimp,
      erw [comp_id, id_comp], },
    { refl, }, }
end

lemma functoriality_N₁ : (simplicial_object.whiskering C D).obj F ⋙
  algebraic_topology.dold_kan.N₁ =
  algebraic_topology.dold_kan.N₁ ⋙ functor_karoubi_homological_complex_obj F :=
begin
  apply functor.ext,
  { intros X Y f,
    ext n,
    simp only [karoubi.comp, homological_complex.comp_f, karoubi.eq_to_hom_f, homological_complex.eq_to_hom_f,
      eq_to_hom_refl, comp_id],
    dsimp,
    simp only [dold_kan.map_P_infty_degreewise, ← F.map_comp],
    congr' 1,
    simp only [assoc, dold_kan.P_infty_degreewise_naturality],
    simp only [← assoc, dold_kan.P_infty_degreewise_is_a_projector], },
  { intro X,
    ext n,
    dsimp,
    rw [homological_complex.eq_to_hom_f, ← algebraic_topology.dold_kan.map_P_infty_degreewise],
    erw [comp_id, id_comp],
    have h := congr_obj (map_alternating_face_map_complex F) X,
    dsimp at ⊢ h,
    simpa only [← h], }
end

lemma functoriality_N : functor_karoubi_simplicial_object.obj F ⋙ dold_kan.equivalence.functor =
  dold_kan.equivalence.functor ⋙ functor_karoubi_homological_complex_obj F :=
begin
  dsimp [functor_karoubi_simplicial_object, functor_karoubi_homological_complex_obj],
  simp only [functor_extension'', functor.comp_obj, N, N₂],
  erw ← functor_extension'_comp (simplicial_object C) (chain_complex C ℕ) (chain_complex D ℕ)
    algebraic_topology.dold_kan.N₁ (F.map_homological_complex (complex_shape.down ℕ) ⋙ to_karoubi _),
  erw ← functor_extension'_comp (simplicial_object C) (simplicial_object D) (chain_complex D ℕ)
    ((simplicial_object.whiskering C D).obj F ⋙ to_karoubi _) N₁,
  congr' 1,
  rw functor.assoc,
  have h := congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _)
    (N₁ : simplicial_object D ⥤ _),
  simp only [functor.comp_obj, whiskering_left, functor.id] at h,
  erw h,
  apply functoriality_N₁,
end

end dold_kan

end preadditive

end category_theory
