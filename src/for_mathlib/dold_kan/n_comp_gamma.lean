/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.gamma_comp_n
import for_mathlib.dold_kan.n_reflects_iso

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open opposite
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]

lemma P_infty_eq_zero_on (X : simplicial_object C) {n : ℕ} {Δ' : simplex_category} (i : Δ' ⟶ [n]) [mono i]
  (h₁ : Δ'.len ≠ n) (h₂ : ¬is_d0 i) :
P_infty.f n ≫ X.map i.op = 0 :=
begin
  have h₃ := simplex_category.len_le_of_mono (show mono i, by apply_instance),
  simp only [simplex_category.len_mk] at h₃,
  cases le_iff_exists_add.mp h₃ with c hc,
  cases c,
  { exfalso, exact h₁ hc.symm, },
  have h₄ : ∃ (m : ℕ), n = m+1 := by { use Δ'.len + c, rw add_assoc, exact hc, },
  cases h₄ with m hm,
  unfreezingI { subst hm, },
  have h₄ : ∃ (k : fin (m+2)), k ≠ 0 ∧ ∀ x, i.to_order_hom x ≠ k,
  { have h₅ : ¬epi i,
    { by_contradiction,
      have h₆ := simplex_category.len_le_of_epi h,
      simp only [simplex_category.len_mk] at h₆,
      rw nat.succ_eq_add_one at hc,
      linarith, },
    rw simplex_category.epi_iff_surjective at h₅,
    simp only [not_forall, not_exists] at h₅,
    cases h₅ with x hx,
    by_cases x = 0, swap,
    { use x,
      exact ⟨h, hx⟩, },
    { subst h,
      rcases simplex_category.eq_comp_δ_of_not_surjective' i 0 hx with ⟨θ, hθ⟩,
      have h₇ : ¬epi θ,
    { by_contradiction,
      have h₈ := simplex_category.len_le_of_epi h,
      simp only [simplex_category.len_mk] at h₈,
      rw nat.succ_eq_add_one at hc,
      have h₉ : Δ' = [m], by { ext, rw simplex_category.len_mk, linarith, },
      unfreezingI { subst h₉, },
      haveI : mono θ := mono_of_mono_fac hθ.symm,
      rw [simplex_category.eq_id_of_mono θ, id_comp] at hθ,
      simpa only [hθ, is_d0_iff] using h₂, },
      rw simplex_category.epi_iff_surjective at h₇,
      simp only [not_forall, not_exists] at h₇,
      cases h₇ with y hy,
      use y.succ,
      split,
      { apply fin.succ_ne_zero, },
      { intros z hz,
        simp only [hθ, simplex_category.hom.comp, simplex_category.small_category_comp,
          simplex_category.hom.to_order_hom_mk, order_hom.comp_coe, function.comp_app] at hz,
        erw [fin.succ_above_above (0 : fin (m+2)) _ (fin.zero_le _), fin.succ_inj] at hz,
        exact hy z hz, }, }, },
  rcases h₄ with ⟨k, ⟨hk₁, hk₂⟩⟩,
  rcases simplex_category.eq_comp_δ_of_not_surjective' i k hk₂ with ⟨θ, hθ⟩,
  haveI : mono θ := mono_of_mono_fac hθ.symm,
  erw [P_infty_degreewise, hθ, op_comp, X.map_comp, ← assoc, ← k.succ_pred hk₁,
    higher_faces_vanish_P (m+1) m (k.pred hk₁) le_add_self, zero_comp],
end

/-
lemma P_infty_eq_zero_on' (X : simplicial_object C) {n : ℕ} {Δ' : simplex_category} (f : op [n] ⟶ op Δ') [mono f.unop]
  (h₁ : Δ'.len ≠ n) (h₂ : ¬is_d0 f.unop) :
  P_infty.f n ≫ X.map f = 0 :=
begin

  have pif := P_infty_eq_zero_on X f.unop h₁ h₂,
  sorry,
--P_infty_eq_zero_on X f.unop h₁ h₂
end-/

lemma Γ_on_mono_comp_P_infty' (X : simplicial_object C) {n n' : ℕ} (i : ([n] : simplex_category) ⟶ [n']) [mono i] :
  Γ_on_mono (alternating_face_map_complex.obj X) i ≫ P_infty.f n = P_infty.f n' ≫ X.map i.op :=
begin
  /- We start with the case `i` is an identity -/
  by_cases n = n',
  { unfreezingI { subst h, },
    have h := simplex_category.eq_id_of_mono i,
    unfreezingI { subst h, },
    simp only [Γ_on_mono_on_id, op_id, eq_to_hom_refl, eq_to_hom_trans, id_comp],
    erw [X.map_id, comp_id], },
  by_cases hi : is_d0 i,
  /- The case `i = δ 0` -/
  { erw [Γ_on_mono_on_d0 _ i hi, ← P_infty.comm' n' n hi.left.symm],
    have h' : n' = n+1 := hi.left,
    unfreezingI { subst h', },
    dsimp [alternating_face_map_complex.obj, chain_complex.of],
    simp only [eq_self_iff_true, id_comp, if_true, preadditive.comp_sum],
    rw finset.sum_eq_single (0 : fin (n+2)), rotate,
    { intros b hb hb',
      simp only [preadditive.comp_zsmul],
      erw [P_infty_eq_zero_on X (simplex_category.δ b) h (by { rw is_d0_iff, exact hb', }), zsmul_zero], },
    { simp only [finset.mem_univ, not_true, forall_false_left], },
    { simpa only [eq_d0_of_is_d0 hi, fin.coe_zero, pow_zero, one_zsmul], }, },
  /- The case `i ≠ δ 0` -/
  { rw [Γ_on_mono_eq_zero _ i _ hi, zero_comp], swap,
    { by_contradiction h',
      exact h (congr_arg simplex_category.len h'.symm), },
    rw P_infty_eq_zero_on,
    { exact h, },
    { by_contradiction h',
      exact hi h', }, },
end

lemma simplex_rewrite (Δ : simplex_category) : ∃ (n : ℕ), Δ = [n] :=
begin
  use Δ.len,
  ext,
  simp only [simplex_category.mk_len],
end

lemma Γ_on_mono_comp_P_infty (X : simplicial_object C) {Δ Δ' : simplex_category} (i : Δ' ⟶ Δ) [mono i] :
  Γ_on_mono (alternating_face_map_complex.obj X) i ≫ P_infty.f (Δ'.len) = P_infty.f (Δ.len) ≫
    X.map (eq_to_hom (by simp only [simplex_category.mk_len]) ≫ i.op ≫ eq_to_hom (by simp only [simplex_category.mk_len])) :=
begin
  cases simplex_rewrite Δ with n h,
  cases simplex_rewrite Δ' with n' h',
  unfreezingI { substs h h', },
  simp only [eq_to_hom_refl, id_comp, comp_id],
  apply Γ_on_mono_comp_P_infty',
end

@[simps]
def Γ₂N₁_nat_trans : (N₁ : simplicial_object C ⥤ _) ⋙ Γ₂ ⟶ to_karoubi _ :=
{ app := λ X,
  { f :=
    { app := λ Δ, sigma.desc (λ A,
        P_infty.f _ ≫ X.map (eq_to_hom (by { simp only [simplex_category.mk_len] }) ≫ A.2.1.op)),
      naturality' := λ Δ Δ' θ, begin
        ext A,
        cases A,
        slice_rhs 1 2 { erw colimit.ι_desc, },
        dsimp,
        let em := image.mono_factorisation (θ.unop ≫ A.2.1),
        haveI : epi em.e := simplex_category.epi_of_mono_factorisation _,
        slice_lhs 1 2 { erw [Γ_simplicial_on_summand _ A em.fac], },
        slice_lhs 2 3 { erw colimit.ι_desc, },
        dsimp,
        slice_lhs 1 2 { erw Γ_on_mono_comp_P_infty, },
        simp only [assoc, ← X.map_comp],
        congr' 2,
        repeat { erw id_comp, },
        rw [← op_comp, em.fac, op_comp],
        refl,
      end },
    comm := begin
      ext Δ A,
      dsimp,
      simp only [colimit.ι_desc],
      dsimp,
      slice_rhs 1 2 { erw ι_colim_map, },
      simp only [discrete.nat_trans_app, cofan.mk_ι_app, colimit.ι_desc,
        eq_to_hom_map, assoc, comp_id, functor.map_comp],
      slice_rhs 1 2 { erw P_infty_degreewise_is_a_projection, },
      simp only [assoc],
    end },
  naturality' := λ X Y f, begin
    ext Δ A,
    simp only [colimit.ι_desc, assoc, functor.map_comp, discrete.nat_trans_app, cofan.mk_ι_app, subtype.val_eq_coe,
      functor.comp_map, karoubi.comp, nat_trans.comp_app, Γ₂_map_f_app, N₁_map_f,
      alternating_face_map_complex.map, alternating_face_map_complex_map, homological_complex.comp_f,
      chain_complex.of_hom_f, ι_colim_map_assoc, to_karoubi_map_f, colimit.ι_desc_assoc, nat_trans.naturality],
    slice_lhs 2 3 { erw P_infty_degreewise_naturality, },
    slice_lhs 1 2 { erw P_infty_degreewise_is_a_projection, },
    slice_lhs 2 3 { erw ← f.naturality, },
    simpa only [← assoc],
  end }

@[simps]
def Γ₂N₂_nat_trans : (N₂ : karoubi (simplicial_object C) ⥤ _) ⋙ Γ₂ ⟶ 𝟭 _ :=
begin
  apply (whiskering_left_to_karoubi_hom_equiv (N₂ ⋙ Γ₂) (𝟭 _)).inv_fun,
  refine eq_to_hom _ ≫ Γ₂N₁_nat_trans,
  { exact congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _) (N₁ ⋙ Γ₂), },
end

lemma identity_N₂_objectwise (P : karoubi (simplicial_object C)) :
N₂Γ₂_iso.inv.app (N₂.obj P) ≫ N₂.map (Γ₂N₂_nat_trans.app P) = 𝟙 (N₂.obj P) :=
begin
  ext n,
  simp only [karoubi.comp, homological_complex.comp_f, N₂Γ₂_iso_inv_app_f_f, N₂_obj_p_f, assoc,
    N₂_map_f_f, Γ₂N₂_nat_trans_app_f_app, karoubi.id_eq],
  have eq₁ : P.p.app (op [n]) ≫ P_infty.f n = P_infty.f n ≫ P.p.app (op [n]) :=
    P_infty_degreewise_naturality _ _,
  have eq₂ : (P_infty : K[P.X] ⟶ _).f n ≫ P_infty.f n = P_infty.f n :=
    P_infty_degreewise_is_a_projection n,
  have eq₃ : P.p.app (op [n]) ≫ P.p.app _ = P.p.app _,
  { simpa only [nat_trans.comp_app] using congr_app P.idem (op [n]), },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  repeat
  { slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
    slice_lhs 3 4 { erw [ι_colim_map, discrete.nat_trans_app], },
    slice_lhs 2 3 { erw eq₁, },
    slice_lhs 1 2 { erw eq₂, },
    slice_lhs 2 3 { erw eq₃, }, },
  slice_lhs 3 4 { erw [ι_colim_map, discrete.nat_trans_app], },
  slice_lhs 2 3 { erw eq₁, },
  slice_lhs 1 2 { erw eq₂, },
  slice_lhs 2 3 { erw comp_id, },
  slice_lhs 3 4 { erw colimit.ι_desc, },
  dsimp only [cofan.mk],
  slice_lhs 3 4 { erw [P.X.map_id, comp_id], },
  slice_lhs 2 3 { erw eq₁, },
  slice_lhs 1 2 { erw eq₂, },
  slice_lhs 2 3 { erw eq₃, },
end

lemma identity_N₂ :
  ((𝟙 (N₂ : karoubi (simplicial_object C) ⥤ _ ) ◫ N₂Γ₂_iso.inv) ≫
  (Γ₂N₂_nat_trans ◫ 𝟙 N₂) : N₂ ⟶ N₂) = 𝟙 N₂ :=
begin
  ext1, ext1 P,
  dsimp,
  erw [Γ₂.map_id, N₂.map_id, comp_id, id_comp],
  exact identity_N₂_objectwise P,
end

instance : is_iso (Γ₂N₂_nat_trans : (N₂ : karoubi (simplicial_object C) ⥤ _ ) ⋙ _ ⟶ _) :=
begin
  have hN : reflects_isomorphisms (N₂ : karoubi (simplicial_object C) ⥤ _) := by apply_instance,
  haveI : ∀ (P : karoubi (simplicial_object C)), is_iso (Γ₂N₂_nat_trans.app P), swap,
  { apply nat_iso.is_iso_of_is_iso_app, },
  intro P,
  haveI : is_iso (N₂.map (Γ₂N₂_nat_trans.app P)), swap,
  { apply hN.reflects, },
  have h' := identity_N₂_objectwise P,
  erw [hom_comp_eq_id] at h',
  rw h',
  apply_instance,
end

lemma Γ₂N₁_nat_trans_compatible_with_Γ₂N₂_nat_trans (X : simplicial_object C) :
  Γ₂N₁_nat_trans.app X =
  eq_to_hom begin
    ext Δ j,
    { simp only [eq_to_hom_refl, comp_id, id_comp], congr' 1, dsimp, congr, ext A, erw comp_id, },
    { refl },
  end ≫ Γ₂N₂_nat_trans.app ((to_karoubi _).obj X) :=
begin
  ext Δ A,
  simp only [karoubi.comp, eq_to_hom_refl, comp_id, karoubi.eq_to_hom_f],
  dsimp [Γ₂N₂_nat_trans, Γ₂N₁_nat_trans],
  simp only [functor.map_comp, eq_to_hom_map, karoubi.eq_to_hom_f, eq_to_hom_refl,
    comp_id, karoubi.decomp_id_p_f, to_karoubi_obj_p, assoc, eq_to_hom_app, karoubi.comp,
    nat_trans.comp_app, Γ₂_map_f_app, N₂_map_f_f, karoubi.decomp_id_i_f, Γ₂_obj_p_app,
    N₂_obj_p_f, ι_colim_map_assoc, discrete.nat_trans_app, colimit.ι_desc,
  cofan.mk_ι_app],
  erw [nat_trans.id_app, nat_trans.id_app, id_comp, id_comp, comp_id,
    colimit.ι_desc, cofan.mk_ι_app],
  repeat { slice_rhs 1 2 { erw P_infty_degreewise_is_a_projection, }, },
  rw assoc,
end

instance : is_iso (Γ₂N₁_nat_trans : (N₁ : simplicial_object C ⥤_ ) ⋙ _ ⟶ _) :=
begin
  haveI : ∀ (X : simplicial_object C), is_iso (Γ₂N₁_nat_trans.app X),
  { intro X,
    rw Γ₂N₁_nat_trans_compatible_with_Γ₂N₂_nat_trans,
    apply is_iso.comp_is_iso, },
  apply nat_iso.is_iso_of_is_iso_app,
end

@[simps]
def Γ₂N₂_iso : 𝟭 _ ≅ (N₂ : karoubi (simplicial_object C) ⥤ _) ⋙ Γ₂ :=
(as_iso Γ₂N₂_nat_trans).symm

@[simps]
def Γ₂N₁_iso : to_karoubi _  ≅ (N₁ : simplicial_object C ⥤ _) ⋙ Γ₂ :=
(as_iso Γ₂N₁_nat_trans).symm

end dold_kan

end algebraic_topology
