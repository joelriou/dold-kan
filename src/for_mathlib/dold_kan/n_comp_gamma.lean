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
open simplex_category
open opposite
open simplicial_object
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]

/- ajouter lemme général un mono est epi sssi égalité des cardinaux, etc. -/

lemma P_infty_comp_map_mono_eq_zero (X : simplicial_object C) {n : ℕ}
  {Δ' : simplex_category} (i : Δ' ⟶ [n]) [mono i]
  (h₁ : Δ'.len ≠ n) (h₂ : ¬is_δ₀ i) :
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
      simpa only [hθ, is_δ₀.iff] using h₂, },
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
  erw [P_infty_f, hθ, op_comp, X.map_comp, ← assoc, ← k.succ_pred hk₁,
    higher_faces_vanish.of_P (m+1) m (k.pred hk₁) le_add_self, zero_comp],
end

@[reassoc]
lemma Γ_on_mono_comp_P_infty (X : simplicial_object C) {Δ Δ' : simplex_category} (i : Δ ⟶ Δ') [mono i] :
  Γ₀.obj.termwise.map_mono (alternating_face_map_complex.obj X) i ≫ P_infty.f (Δ.len) = P_infty.f (Δ'.len) ≫
    X.map i.op :=
begin
  unfreezingI
  { induction Δ using simplex_category.rec with n,
    induction Δ' using simplex_category.rec with n', },
  dsimp,
  /- We start with the case `i` is an identity -/
  by_cases n = n',
  { unfreezingI { subst h, },
    simp only [simplex_category.eq_id_of_mono i, Γ₀.obj.termwise.map_mono_id,
      op_id, X.map_id],
    dsimp,
    simp only [id_comp, comp_id], },
  by_cases hi : is_δ₀ i,
  /- The case `i = δ 0` -/
  { have h' : n' = n+1 := hi.left,
    unfreezingI { subst h', },
    rw Γ₀.obj.termwise.map_mono_δ₀' _ i hi,
    dsimp,
    rw ← P_infty.comm' _ n rfl,
    dsimp [alternating_face_map_complex.obj, chain_complex.of],
    simp only [eq_self_iff_true, id_comp, if_true, preadditive.comp_sum],
    rw finset.sum_eq_single (0 : fin (n+2)), rotate,
    { intros b hb hb',
      simp only [preadditive.comp_zsmul],
      erw [P_infty_comp_map_mono_eq_zero X (simplex_category.δ b) h (by { rw is_δ₀.iff, exact hb', }), zsmul_zero], },
    { simp only [finset.mem_univ, not_true, is_empty.forall_iff], },
    { simpa only [hi.eq_δ₀, fin.coe_zero, pow_zero, one_zsmul], }, },
  /- The case `i ≠ δ 0` -/
  { rw [Γ₀.obj.termwise.map_mono_eq_zero _ i _ hi, zero_comp], swap,
    { by_contradiction h',
      exact h (congr_arg simplex_category.len h'.symm), },
    rw P_infty_comp_map_mono_eq_zero,
    { exact h, },
    { by_contradiction h',
      exact hi h', }, },
end

namespace Γ₂N₁

@[simps]
def nat_trans : (N₁ : simplicial_object C ⥤ _) ⋙ Γ₂ ⟶ to_karoubi _ :=
{ app := λ X,
  { f :=
    { app := λ Δ, (Γ₀.splitting K[X]).desc Δ (λ A, P_infty.f A.1.unop.len ≫ X.map (A.e.op)),
      naturality' := λ Δ Δ' θ, begin
        apply (Γ₀.splitting K[X]).hom_ext',
        intro A,
        change _ ≫ (Γ₀.obj K[X]).map θ  ≫ _ = _,
        simp only [splitting.ι_desc_assoc, assoc,
          Γ₀.obj.map_on_summand'_assoc K[X] A θ, splitting.ι_desc],
        erw Γ_on_mono_comp_P_infty_assoc X (image.ι (θ.unop ≫ A.e)),
        dsimp only [to_karoubi],
        simp only [← X.map_comp],
        congr' 2,
        simp only [eq_to_hom_refl, id_comp, comp_id, ← op_comp],
        apply quiver.hom.unop_inj,
        exact A.fac_pull θ,
      end, },
    comm := begin
      apply (Γ₀.splitting K[X]).hom_ext,
      intro n,
      dsimp [N₁],
      simp only [← splitting.ι_summand_id, splitting.ι_desc,
        comp_id, splitting.ι_desc_assoc, assoc, P_infty_f_idem_assoc],
    end, },
  naturality' := λ X Y f, begin
    ext1,
    apply (Γ₀.splitting K[X]).hom_ext,
    intro n,
    dsimp [N₁, to_karoubi],
    simpa only [← splitting.ι_summand_id, splitting.ι_desc,
      splitting.ι_desc_assoc, assoc, karoubi.comp, nat_trans.comp_app,
      Γ₂_map_f_app, homological_complex.comp_f, alternating_face_map_complex.map_f,
      P_infty_f_naturality_assoc, P_infty_f_idem_assoc, nat_trans.naturality],
  end, }

end Γ₂N₁

@[simps]
def compatibility_Γ₂N₁_Γ₂N₂ : to_karoubi (simplicial_object C) ⋙ N₂ ⋙ Γ₂ ≅ N₁ ⋙ Γ₂ :=
eq_to_iso (functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi _ _) (N₁ ⋙ Γ₂))

namespace Γ₂N₂

@[simps]
def nat_trans : (N₂ : karoubi (simplicial_object C) ⥤ _) ⋙ Γ₂ ⟶ 𝟭 _ :=
(whiskering_left_to_karoubi_hom_equiv (N₂ ⋙ Γ₂) (𝟭 _)).inv_fun
    (compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.nat_trans)

end Γ₂N₂

lemma identity_N₂_objectwise_eq₁ (P : karoubi (simplicial_object C)) (n : ℕ):
  (N₂Γ₂.inv.app (N₂.obj P)).f.f n = P_infty.f n ≫ P.p.app (op [n]) ≫
  (Γ₀.splitting (N₂.obj P).X).ι_summand (splitting.index_set.id (op [n])) :=
by simp only [N₂Γ₂_inv_app_f_f, N₂_obj_p_f, assoc]

lemma identity_N₂_objectwise_eq₂ (P : karoubi (simplicial_object C)) (n : ℕ):
  (Γ₀.splitting (N₂.obj P).X).ι_summand (splitting.index_set.id (op [n]))
  ≫ (N₂.map (Γ₂N₂.nat_trans.app P)).f.f n = P_infty.f n ≫ P.p.app (op [n]) :=
begin
  simp only [N₂_map_f_f, Γ₂N₂.nat_trans_app_f_app, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
    splitting.ι_desc_assoc, assoc],
  dsimp [to_karoubi, N₂],
  change _ ≫  _ ≫ (Γ₀.splitting K[P.X]).ι_summand _ ≫ _ = _,
  simp only [id_comp, splitting.ι_desc_assoc, assoc, nat_trans.naturality,
    P_infty_f_idem_assoc],
  erw P.X.map_id,
  dsimp [splitting.index_set.id, splitting.index_set.e],
  simp only [comp_id, P_infty_f_naturality_assoc, app_idem, P_infty_f_idem_assoc],
end

lemma identity_N₂_objectwise (P : karoubi (simplicial_object C)) :
  N₂Γ₂.inv.app (N₂.obj P) ≫ N₂.map (Γ₂N₂.nat_trans.app P) = 𝟙 (N₂.obj P) :=
begin
  ext n,
  simp only [karoubi.comp, homological_complex.comp_f, karoubi.id_eq, N₂_obj_p_f, assoc,
    identity_N₂_objectwise_eq₁, identity_N₂_objectwise_eq₂, P_infty_f_naturality_assoc,
    app_idem, P_infty_f_idem_assoc],
end

lemma identity_N₂ :
  ((𝟙 (N₂ : karoubi (simplicial_object C) ⥤ _ ) ◫ N₂Γ₂.inv) ≫
  (Γ₂N₂.nat_trans ◫ 𝟙 N₂) : N₂ ⟶ N₂) = 𝟙 N₂ :=
begin
  ext1, ext1 P,
  dsimp,
  erw [Γ₂.map_id, N₂.map_id, comp_id, id_comp],
  exact identity_N₂_objectwise P,
end

instance : is_iso (Γ₂N₂.nat_trans : (N₂ : karoubi (simplicial_object C) ⥤ _ ) ⋙ _ ⟶ _) :=
begin
  have hN : reflects_isomorphisms (N₂ : karoubi (simplicial_object C) ⥤ _) := by apply_instance,
  haveI : ∀ (P : karoubi (simplicial_object C)), is_iso (Γ₂N₂.nat_trans.app P), swap,
  { apply nat_iso.is_iso_of_is_iso_app, },
  intro P,
  haveI : is_iso (N₂.map (Γ₂N₂.nat_trans.app P)), swap,
  { apply hN.reflects, },
  have h' := identity_N₂_objectwise P,
  erw [hom_comp_eq_id] at h',
  rw h',
  apply_instance,
end

lemma compatibility_Γ₂N₁_Γ₂N₂_nat_trans (X : simplicial_object C) :
  Γ₂N₁.nat_trans.app X = (compatibility_Γ₂N₁_Γ₂N₂.app X).inv ≫
    Γ₂N₂.nat_trans.app ((to_karoubi _).obj X) :=
begin
  ext1,
  apply (Γ₀.splitting (N₁.obj X).X).hom_ext,
  intro n,
  simp only [simplicial_object.splitting.φ, Γ₂N₁.nat_trans_app_f_app, karoubi.eq_to_hom_f,
    eq_to_hom_refl, comp_id, iso.app_inv, compatibility_Γ₂N₁_Γ₂N₂_inv, eq_to_hom_app,
    karoubi.comp, nat_trans.comp_app, Γ₂N₂.nat_trans_app_f_app, to_karoubi_obj_p],
  dsimp [N₁, N₂],
  simp only [← splitting.ι_summand_id, splitting.ι_desc,
    id_comp, comp_id, splitting.ι_desc_assoc, assoc, P_infty_f_idem_assoc],
  change _ = _ ≫ (Γ₀.splitting K[X]).ι_summand (splitting.index_set.id (op [n])) ≫ _,
  simp only [splitting.ι_desc_assoc, assoc, splitting.ι_desc, P_infty_f_idem_assoc],
end

instance : is_iso (Γ₂N₁.nat_trans : (N₁ : simplicial_object C ⥤_ ) ⋙ _ ⟶ _) :=
begin
  haveI : ∀ (X : simplicial_object C), is_iso (Γ₂N₁.nat_trans.app X),
  { intro X,
    rw compatibility_Γ₂N₁_Γ₂N₂_nat_trans,
    apply is_iso.comp_is_iso, },
  apply nat_iso.is_iso_of_is_iso_app,
end

@[simps]
def Γ₂N₂ : 𝟭 _ ≅ (N₂ : karoubi (simplicial_object C) ⥤ _) ⋙ Γ₂ :=
(as_iso Γ₂N₂.nat_trans).symm

@[simps]
def Γ₂N₁ : to_karoubi _  ≅ (N₁ : simplicial_object C ⥤ _) ⋙ Γ₂ :=
(as_iso Γ₂N₁.nat_trans).symm

end dold_kan

end algebraic_topology
