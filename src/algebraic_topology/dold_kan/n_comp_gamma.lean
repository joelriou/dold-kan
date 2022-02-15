/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.gamma_comp_n
import algebraic_topology.dold_kan.n_reflects_iso
import for_mathlib.idempotents.nat_trans

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
--open category_theory.preadditive
open category_theory.idempotents
--open category_theory.simplicial_object
--open homotopy
open opposite
open_locale simplicial

universe v

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category.{v} C] [additive_category C]

@[simps]
def ΓN'_trans : (N' : simplicial_object C ⥤ _) ⋙ Γ
  ⟶ to_karoubi _ :=
{ app := λ X,
  { f :=
    { app := λ Δ, sigma.desc (λ A,
        P_infty.f _ ≫ X.map (eq_to_hom (by { simp only [simplex_category.mk_len] }) ≫ A.2.1.op)),
      naturality' := sorry, },
    comm := sorry, },
  naturality' := sorry }

@[simps]
def ΓN_trans : (N : karoubi (simplicial_object C) ⥤ _) ⋙ Γ ⟶ 𝟭 _ :=
begin
  apply (whiskering_left_to_karoubi_hom_equiv (N ⋙ Γ) (𝟭 _)).inv_fun,
  refine eq_to_hom _ ≫ ΓN'_trans,
  { exact congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _) (N' ⋙ Γ), },
end

lemma identity_N : ((𝟙 (N : karoubi (simplicial_object C) ⥤_ ) ◫ NΓ.inv) ≫ (ΓN_trans ◫ 𝟙 N) : N ⟶ N) = 𝟙 N :=
begin
  ext P n,
  simp only [assoc, nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app,
    karoubi.id_eq, functor.comp_map, karoubi.comp, nat_trans.hcomp_id_app,
    homological_complex.comp_f, NΓ_inv_app_f_f, N_obj_p_f, N_map_f_f, Γ_map_f_app,
    ΓN_trans_app_f_app],
  have eq₁ : P_infty.f n ≫ P_infty.f n = P_infty.f n := P_infty_degreewise_is_a_projector n,
  have eq₂ : P.p.app (op [n]) ≫ P.p.app _ = P.p.app _,
  { simpa only [nat_trans.comp_app] using congr_app P.idempotence (op [n]), },
  have eq₃ : P.p.app (op [n]) ≫ P_infty.f n = P_infty.f n ≫ P.p.app (op [n]) :=
    P_infty_degreewise_naturality _ _,
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw [ι_colim_map, discrete.nat_trans_app], },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw [ι_colim_map, discrete.nat_trans_app], },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw [ι_colim_map, discrete.nat_trans_app], },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw [ι_colim_map, discrete.nat_trans_app], },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw comp_id, },
  slice_lhs 3 4 { erw colimit.ι_desc, },
  dsimp only [cofan.mk],
  slice_lhs 3 4 { erw comp_id, },
  slice_lhs 3 4 { erw [P.X.map_id, comp_id], },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
end

instance : is_iso (ΓN_trans : (N : karoubi (simplicial_object C) ⥤_ ) ⋙ _ ⟶ _) :=
begin
  have hN : reflects_isomorphisms (N : karoubi (simplicial_object C) ⥤ _) := by apply_instance,
  haveI : ∀ (P : karoubi (simplicial_object C)), is_iso (ΓN_trans.app P), swap,
  { apply nat_iso.is_iso_of_is_iso_app, },
  intro P,
  haveI : is_iso (N.map (ΓN_trans.app P)), swap,
  { apply hN.reflects, },
  have h := congr_app identity_N P,
  simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app] at h,
  erw [(Γ ⋙ N).map_id, comp_id, id_comp, hom_comp_eq_id] at h,
  rw h,
  apply_instance,
end

lemma ΓN_trans_app_to_karoubi (X : simplicial_object C) :
  ΓN_trans.app ((to_karoubi (simplicial_object C)).obj X) = eq_to_hom
  (by { ext Δ j, { simp only [eq_to_hom_refl, comp_id, id_comp], congr' 1, dsimp, congr, ext A, erw comp_id, },
    { refl,}, }) ≫ ΓN'_trans.app X  :=
begin
  ext Δ A,
  simp only [karoubi.comp, eq_to_hom_refl, comp_id, karoubi.eq_to_hom_f],
  dsimp [ΓN_trans, ΓN'_trans],
  simp,
  repeat { erw nat_trans.id_app, },
  erw [comp_id, id_comp, id_comp],
  slice_lhs 1 2 { erw P_infty_degreewise_is_a_projector, },
  erw assoc,
end

lemma is_iso_cancel_comp_left {D : Type*} [category D] {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : is_iso f]
  [hfg : is_iso (f ≫ g)] : is_iso g :=
begin
  refine ⟨_⟩,
  use inv (f ≫ g) ≫ f,
  split,
  { conv { to_lhs, congr, rw [← id_comp g, ← is_iso.inv_hom_id f], },
    slice_lhs 2 4 { rw [← assoc, is_iso.hom_inv_id], },
    rw [id_comp, is_iso.inv_hom_id], },
  { rw [assoc, is_iso.inv_hom_id], },
end

instance : is_iso (ΓN'_trans : (N' : simplicial_object C ⥤_ ) ⋙ _ ⟶ _) :=
begin
  haveI : ∀ (X : simplicial_object C), is_iso (ΓN'_trans.app X), swap,
  { apply nat_iso.is_iso_of_is_iso_app, },
  intro X,
  have h : is_iso (ΓN_trans.app ((to_karoubi _).obj X)) := by apply_instance,
  rw ΓN_trans_app_to_karoubi at h,
  exact @is_iso_cancel_comp_left _ _ _ _ _ _ _ infer_instance h,
end

@[simps]
def ΓN : (N : karoubi (simplicial_object C) ⥤ _) ⋙ Γ ≅ 𝟭 _ := as_iso (ΓN_trans)

end dold_kan

end algebraic_topology
