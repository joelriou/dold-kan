/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.functor_n
import for_mathlib.dold_kan.decomposition
import for_mathlib.idempotents.karoubi_karoubi
import for_mathlib.idempotents.homological_complex

open category_theory
open category_theory.category
open category_theory.idempotents
open opposite
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

open morph_components

instance : reflects_isomorphisms
  (N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
begin
  constructor,
  intros X Y f,
  introI,
  /- restating the result in a way that allows induction on the degree n -/
  suffices : ∀ (n : ℕ), is_iso (f.app (op [n])),
  { haveI : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (f.app Δ) := λ Δ, this Δ.unop.len,
    apply nat_iso.is_iso_of_is_iso_app, },
  /- restating the assumption in a more practical form -/
  have h  := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.hom_inv_id (N₁.map f))),
  have h' := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.inv_hom_id (N₁.map f))),
  have h'' := λ n, karoubi.homological_complex.p_comm_degreewise_assoc (inv (N₁.map f)) (n)
    (f.app (op [n])),
  simp only [N₁_map_f, karoubi.comp, homological_complex.comp_f,
    alternating_face_map_complex.map_f, N₁_obj_p, karoubi.id_eq, assoc] at h h' h'',
  /- we have to construct an inverse to f in degree n, by induction on n -/
  intro n,
  induction n with n hn,
  /- degree 0 -/
  { use (inv (N₁.map f)).f.f 0,
    have h₀ := h 0,
    have h'₀ := h' 0,
    dsimp at h₀ h'₀,
    simp only [id_comp, comp_id] at h₀ h'₀,
    split; assumption, },
  /- induction step -/
  { haveI := hn,
    use φ
      { a := P_infty.f (n+1) ≫ (inv (N₁.map f)).f.f (n+1),
        b := λ i, inv (f.app (op [n])) ≫ X.σ i, },
    simp only [← φ_id, ← pre_comp_φ, pre_comp, morph_components.id,
      ← post_comp_φ, post_comp, P_infty_degreewise_naturality_assoc,
      is_iso.hom_inv_id_assoc, assoc, is_iso.inv_hom_id_assoc,
      simplicial_object.naturality_σ, h, h', h''],
    split; refl, },
end

lemma karoubi_alternating_face_map_complex_d (X : karoubi (simplicial_object C)) (n : ℕ) :
  ((((alternating_face_map_complex (karoubi C)).obj
    ((karoubi_functor_category_embedding _ _).obj X)).d (n+1) n).f : X.X _[n+1] ⟶ X.X _[n])
  = X.p.app (op [n+1]) ≫ (((alternating_face_map_complex C).obj X.X).d (n+1) n) ≫ X.p.app (op [n]) :=
begin
  let F := karoubi_functor_category_embedding simplex_categoryᵒᵖ C,
  let G := alternating_face_map_complex (karoubi C),
  have h₁₄ := karoubi.hom_ext.mp (((F ⋙ G).map (𝟙 X)).comm' (n+1) n rfl).symm,
  dsimp only [F, G] at h₁₄,
  conv at h₁₄ { to_lhs, erw functor.map_id', },
  simp only [homological_complex.id_f, comp_id] at h₁₄,
  rw [karoubi.decomp_id, functor.map_comp, homological_complex.comp_f, assoc] at h₁₄,
  erw ((F ⋙ G).map (karoubi.decomp_id_p X)).comm' (n+1) n rfl at h₁₄,
  simp only [karoubi.comp] at h₁₄,
  dsimp at h₁₄,
  have h₄₃ := homological_complex.congr_d (congr_arg alternating_face_map_complex.obj
    (congr_obj (to_karoubi_comp_karoubi_functor_category_embedding _ C) X.X)) (n+1) n rfl,
  simp only [eq_to_hom_refl, comp_id, id_comp] at h₄₃,
  have h₂₃ := karoubi.hom_ext.mp (homological_complex.congr_d
    (congr_obj (map_alternating_face_map_complex (to_karoubi C)) X.X) (n+1) n rfl),
  simp only [functor.comp_obj, eq_to_hom_refl, comp_id, id_comp,
    functor.map_homological_complex_obj_d, karoubi.comp, to_karoubi_map_f, karoubi.id_eq] at h₂₃,
  dsimp at h₂₃,
  simp only [id_comp, comp_id] at h₂₃,
  erw [h₂₃, ← h₄₃, ← h₁₄],
  refl,
end

instance : reflects_isomorphisms
  (N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)) :=
begin
  constructor,
  intros X Y f,
  introI,
  -- the following four functors reflects isomorphisms so that
  -- it suffices to show that `f` become an isomorphism after
  -- applying `F1 ⋙ F2 ⋙ F3 ⋙ F4`
  let F1 := karoubi_functor_category_embedding simplex_categoryᵒᵖ C,
  let F2 : simplicial_object (karoubi C) ⥤ _ := N₁,
  let F3 := (karoubi_chain_complex_equivalence (karoubi C) ℕ).functor,
  let F4 := functor.map_homological_complex (karoubi_karoubi.equivalence C).inverse
    (complex_shape.down ℕ),
  haveI : is_iso ((F1 ⋙ F2 ⋙ F3 ⋙ F4).map f), swap,
  { exact is_iso_of_reflects_iso f (F1 ⋙ F2 ⋙ F3 ⋙ F4), },
  -- `f` becomes an isomorphism after the application of `N ⋙ F5`, so that
  -- it suffices to show the equality of functors `F1 ⋙ F2 ⋙ F3 ⋙ F4 = N ⋙ F5`
  let F5 := (karoubi_chain_complex_equivalence C ℕ).functor,
  have eq : F1 ⋙ F2 ⋙ F3 ⋙ F4 = N₂ ⋙ F5, swap,
  { rw eq,
    simp only [functor.comp_map],
    exact functor.map_is_iso F5 (N₂.map f), },
  -- proof of the equality of functors `F1 ⋙ F2 ⋙ F3 ⋙ F4 = N ⋙ F5`
  apply category_theory.functor.ext,
  { intros P Q f,
    ext n,
    dsimp [F3, F5],
    simp [karoubi_P_infty_f, ← nat_trans.comp_app f.f Q.p,
      congr_app (karoubi.comp_p f) (op [n])], },
  { intro P,
    apply homological_complex.ext,
    { intros i j hij,
      ext,
      dsimp [F3, F5],
      simp only [karoubi.comp, karoubi.eq_to_hom_f, eq_to_hom_refl,
        karoubi_karoubi.inverse_map_f, karoubi_karoubi.inverse_obj_p,
        karoubi_chain_complex_equivalence_functor_obj_d_f,
        karoubi_chain_complex_equivalence_functor_obj_X_p, comp_id, assoc],
      have h := karoubi.hom_ext.mp (homological_complex.congr_hom (N₁.obj
        ((karoubi_functor_category_embedding _ _).obj P)).idem j),
      simp only [homological_complex.comp_f, karoubi.comp] at h,
      conv { to_lhs, congr, skip, erw h, },
      dsimp only [N₁],
      simp only [N₂_obj_p_f],
      have h : j+1=i := hij,
      subst h,
      erw karoubi_alternating_face_map_complex_d P j,
      repeat { erw karoubi_P_infty_f, },
      have eq := congr_app P.idem (op [j]),
      simp only [nat_trans.comp_app] at eq,
      slice_lhs 3 4 { rw eq, },
      slice_lhs 3 4 { rw P_infty_degreewise_naturality, },
      slice_rhs 2 3 { erw P_infty.comm (j+1) j, },
      slice_rhs 3 4 { rw P_infty_degreewise_is_a_projection, },
      refl, },
    { ext n,
      { dsimp,
        simp only [karoubi_P_infty_f, comp_id, id_comp, P_infty_degreewise_naturality], },
      { refl, }, }, }
end

end dold_kan

end algebraic_topology
