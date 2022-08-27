/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.equivalence_additive

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open algebraic_topology

open algebraic_topology.dold_kan

namespace category_theory

namespace simplicial_object

@[simps]
def karoubi_whiskering (C D : Type*) [category C] [category D] :=
simplicial_object.whiskering C D ⋙ functor_extension₂ _ _

end simplicial_object

namespace preadditive

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]
variables {D : Type*} [category D] [preadditive D] [has_finite_coproducts D]
variables (F : C ⥤ D) [functor.additive F]

lemma functoriality_N₁ : (simplicial_object.whiskering C D).obj F ⋙ N₁ =
  N₁ ⋙ F.map_karoubi_homological_complex _ :=
begin
  apply functor.ext,
  { intros X Y f,
    ext n,
    simp only [karoubi.comp, homological_complex.comp_f, karoubi.eq_to_hom_f,
      homological_complex.eq_to_hom_f, eq_to_hom_refl, comp_id],
    dsimp,
    simp only [map_P_infty_f, ← F.map_comp],
    congr' 1,
    rw [assoc, P_infty_f_naturality],
    simp only [← assoc, P_infty_f_idem], },
  { intro X,
    ext n,
    { dsimp,
      erw [homological_complex.eq_to_hom_f, ← algebraic_topology.dold_kan.map_P_infty_f,
      comp_id, id_comp], },
    { exact functor.congr_obj (map_alternating_face_map_complex F).symm X, }, },
end

lemma functoriality_N :
  (simplicial_object.karoubi_whiskering _ _).obj F ⋙ dold_kan.equivalence.functor =
  dold_kan.equivalence.functor ⋙ F.map_karoubi_homological_complex _ :=
begin
  dsimp [functor.map_karoubi_homological_complex,
    simplicial_object.karoubi_whiskering],
  simp only [functor_extension₂, functor.comp_obj, N, N₂],
  erw ← functor_extension₁_comp _ _ _ N₁ (F.map_homological_complex _ ⋙ to_karoubi _),
  erw ← functor_extension₁_comp _ _ _
    ((simplicial_object.whiskering C D).obj F ⋙ to_karoubi _) N₁,
  congr' 1,
  have h := functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi _ _)
    (N₁ : simplicial_object D ⥤ _),
  simp only [functor.comp_obj, whiskering_left, functor.id] at h,
  erw [functor.assoc_eq, h],
  apply functoriality_N₁,
end

end dold_kan

end preadditive

end category_theory
