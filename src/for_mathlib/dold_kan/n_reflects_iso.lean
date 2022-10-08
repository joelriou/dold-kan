/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.functor_n
import for_mathlib.dold_kan.decomposition
import category_theory.idempotents.karoubi_karoubi
import for_mathlib.idempotents.homological_complex
import for_mathlib.idempotents.karoubi_misc

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
⟨λ X Y f, begin
  introI,
  /- restating the result in a way that allows induction on the degree n -/
  suffices : ∀ (n : ℕ), is_iso (f.app (op [n])),
  { haveI : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (f.app Δ) := λ Δ, this Δ.unop.len,
    apply nat_iso.is_iso_of_is_iso_app, },
  /- restating the assumption in a more practical form -/
  have h₁ := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.hom_inv_id (N₁.map f))),
  have h₂ := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.inv_hom_id (N₁.map f))),
  have h₃ := λ n, karoubi.homological_complex.f_p_comm_assoc (inv (N₁.map f)) (n) (f.app (op [n])),
  simp only [N₁_map_f, karoubi.comp, homological_complex.comp_f,
    alternating_face_map_complex.map_f, N₁_obj_p, karoubi.id_eq, assoc] at h₁ h₂ h₃,
  /- we have to construct an inverse to f in degree n, by induction on n -/
  intro n,
  induction n with n hn,
  /- degree 0 -/
  { use (inv (N₁.map f)).f.f 0,
    have h₁₀ := h₁ 0,
    have h₂₀ := h₂ 0,
    dsimp at h₁₀ h₂₀,
    simp only [id_comp, comp_id] at h₁₀ h₂₀,
    tauto, },
  /- induction step -/
  { haveI := hn,
    use φ
      { a := P_infty.f (n+1) ≫ (inv (N₁.map f)).f.f (n+1),
        b := λ i, inv (f.app (op [n])) ≫ X.σ i, },
    simp only [morph_components.id, ← id_φ, ← pre_comp_φ, pre_comp, ← post_comp_φ,
      post_comp, P_infty_f_naturality_assoc, is_iso.hom_inv_id_assoc, assoc,
      is_iso.inv_hom_id_assoc, simplicial_object.σ_naturality, h₁, h₂, h₃],
    tauto, },
end⟩

lemma karoubi_alternating_face_map_complex_d (P : karoubi (simplicial_object C)) (n : ℕ) :
  (((alternating_face_map_complex.obj (karoubi_functor_category_embedding.obj P)).d (n+1) n).f) =
    P.p.app (op [n+1]) ≫ ((alternating_face_map_complex.obj P.X).d (n+1) n) :=
begin
  dsimp,
  simpa only [alternating_face_map_complex.obj_d_eq, karoubi.sum_hom,
    preadditive.sum_comp, preadditive.comp_sum,
    karoubi.zsmul_hom, preadditive.zsmul_comp, preadditive.comp_zsmul],
end

lemma compatibility_N₂_N₁_karoubi :
  N₂ ⋙ (karoubi_chain_complex_equivalence C ℕ).functor =
  karoubi_functor_category_embedding simplex_categoryᵒᵖ C ⋙ N₁ ⋙
  (karoubi_chain_complex_equivalence (karoubi C) ℕ).functor ⋙
  functor.map_homological_complex (karoubi_karoubi.equivalence C).inverse
    (complex_shape.down ℕ) :=
begin
  apply category_theory.functor.ext,
  { intros P Q f,
    ext n,
    dsimp [karoubi_karoubi.inverse, karoubi_functor_category_embedding,
      karoubi_functor_category_embedding.map],
    simp only [karoubi.comp, karoubi.eq_to_hom_f, eq_to_hom_refl, comp_id, assoc,
      karoubi_chain_complex_equivalence_functor_obj_X_p, N₂_obj_p_f,
      homological_complex.eq_to_hom_f, karoubi_P_infty_f, app_p_comm,
      P_infty_f_naturality, P_infty_f_naturality_assoc,
      P_infty_f_idem_assoc, app_comp_p], },
  { intro P,
    apply homological_complex.ext,
    { intros i j hij,
      have h : j+1=i := hij,
      subst h,
      ext,
      dsimp [N₂, N₁, functor_extension₁.obj, karoubi_chain_complex_equivalence,
        karoubi_homological_complex.functor.obj, karoubi_karoubi.inverse],
      have h := (alternating_face_map_complex.map P.p).comm (j+1) j,
      dsimp at h,
      simp only [assoc, karoubi.comp, karoubi.eq_to_hom_f, karoubi_P_infty_f,
        eq_to_hom_refl, comp_id, ← homological_complex.hom.comm_assoc, ← h,
        karoubi_alternating_face_map_complex_d, app_idem_assoc], },
    { ext n,
      { dsimp,
        simp only [comp_id, id_comp, karoubi_P_infty_f, P_infty_f_naturality], },
      { refl, }, }, },
end

/-- We deduce that `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ))`
reflects isomorphisms from the fact that
`N₁ : simplicial_object (karoubi C) ⥤ karoubi (chain_complex (karoubi C) ℕ)` does. -/
instance : reflects_isomorphisms
  (N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)) := ⟨λ X Y f,
begin
  introI,
  -- The following functor `F` reflects isomorphism because it is
  -- a composition of four functors which reflects isomorphisms.
  -- Then, it suffices to show that `F.map f` is an isomorphism.
  let F := karoubi_functor_category_embedding simplex_categoryᵒᵖ C ⋙ N₁ ⋙
    (karoubi_chain_complex_equivalence (karoubi C) ℕ).functor ⋙
    functor.map_homological_complex (karoubi_karoubi.equivalence C).inverse
      (complex_shape.down ℕ),
  haveI : is_iso (F.map f),
  { dsimp only [F],
    rw [← compatibility_N₂_N₁_karoubi, functor.comp_map],
    apply functor.map_is_iso, },
  exact is_iso_of_reflects_iso f F,
end⟩

end dold_kan

end algebraic_topology
