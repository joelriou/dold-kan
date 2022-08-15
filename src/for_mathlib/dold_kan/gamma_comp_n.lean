/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.functor_n
import for_mathlib.dold_kan.degeneracies
import for_mathlib.idempotents.nat_trans

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open simplex_category
open opposite
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]

@[reassoc]
lemma P_infty_on_Γ₀_splitting_summand_eq_zero
  (K : chain_complex C ℕ)
  (n : ℕ) {A : simplex_category.splitting_index_set [n]}
  (hA : A ≠ simplex_category.splitting_index_set.id [n]) :
  (Γ₀.splitting K).ι_summand A ≫ (P_infty : K[Γ₀.obj K] ⟶ _).f n = 0 :=
P_infty_on_splitting_eq_zero (Γ₀.splitting K) A hA

@[simp, reassoc]
lemma P_infty_on_Γ₀_splitting_summand_eq_self
  (K : chain_complex C ℕ) {n : ℕ} :
  (Γ₀.splitting K).ι_summand (simplex_category.splitting_index_set.id [n]) ≫ (P_infty : K[Γ₀.obj K] ⟶ _).f n =
    (Γ₀.splitting K).ι_summand (simplex_category.splitting_index_set.id [n]) :=
begin
  rw P_infty_f,
  cases n,
  { simpa only [P_f_0_eq] using comp_id _, },
  { apply higher_faces_vanish.comp_P_eq_self,
    intros j hj,
    have eq := Γ₀.obj.map_mono_on_summand_id K (simplex_category.δ j.succ),
    rw [Γ₀.obj.termwise.map_mono_eq_zero K, zero_comp] at eq, rotate,
    { intro h,
      exact (nat.succ_ne_self n) (congr_arg simplex_category.len h), },
    { intro h,
      simp only [is_d₀.iff] at h,
      exact fin.succ_ne_zero j h, },
    exact eq, },
end

/-@[simp, reassoc]
lemma ι_Γ₀_summand_comp_P_infty_eq_zero (K : chain_complex C ℕ) {n : ℕ} {A : splitting_index_set [n]} (hA : ¬A = splitting_index_set.id [n]) :
  ι_Γ₀_summand K A ≫ P_infty.f n = 0 :=
begin
  rw [← eq_ι_Γ₀_summand K A, assoc, P_infty_on_degeneracies _ A.e, comp_zero],
  intro h,
  apply hA,
  rw splitting_index_set.eq_id_iff',
  simpa only [fintype.card_fin, add_left_inj] using (fintype.card_of_bijective
    ⟨h, simplex_category.epi_iff_surjective.mp (infer_instance : epi A.e)⟩).symm,
end

@[simp, reassoc]
lemma ι_Γ₀_summand_id_comp_P_infty (K : chain_complex C ℕ) (n : ℕ) :
  ι_Γ₀_summand K (splitting_index_set.id [n]) ≫ (P_infty : K[Γ₀.obj K] ⟶ _ ).f n =
    ι_Γ₀_summand K (splitting_index_set.id [n]) :=
begin
  rw P_infty_f,
  cases n,
  { erw [P_f_0_eq, comp_id], },
  { apply higher_faces_vanish.comp_P_eq_self,
    intros j hj,
    have eq := ι_Γ₀_summand_comp_map_mono K (simplex_category.δ j.succ),
    rw [Γ₀.obj.termwise.map_mono_eq_zero K, zero_comp] at eq, rotate,
    { intro h,
      apply nat.succ_ne_self n,
      exact congr_arg simplex_category.len h, },
    { intro h,
      simp only [is_d₀.iff] at h,
      exact fin.succ_ne_zero j h, },
    exact eq, },
end-/

namespace N₁Γ₀

def hom_app_f_f_termwise (K : chain_complex C ℕ) (n : ℕ) (A : splitting_index_set [n]) :
Γ₀.obj.summand K [n] A ⟶ K.X n :=
  --((to_karoubi (chain_complex C ℕ)).obj K).X.X n :=
begin
  by_cases A = splitting_index_set.id [n],
  { subst h,
    exact 𝟙 _, },
  { exact 0, }
end

@[simp]
lemma hom_app_f_f_termwise_eq_id (K : chain_complex C ℕ) (n : ℕ) :
hom_app_f_f_termwise K n (splitting_index_set.id [n]) = 𝟙 _ :=
begin
  dsimp [hom_app_f_f_termwise],
  simp only [eq_self_iff_true, if_true],
end

lemma hom_app_f_f_termwise_eq_zero (K : chain_complex C ℕ) (n : ℕ)
  {A : splitting_index_set [n]} (h : ¬ A = splitting_index_set.id [n]) :
hom_app_f_f_termwise K n A = 0 :=
begin
  dsimp [hom_app_f_f_termwise],
  split_ifs,
  refl,
end

@[simp]
def hom_app_f_f (K : chain_complex C ℕ) (n : ℕ) :
  (Γ₀.obj K) _[n] ⟶ K.X n :=
(Γ₀.splitting K).desc (op [n]) (hom_app_f_f_termwise K n)

@[simp, reassoc]
lemma ι_hom_app_f_f (K : chain_complex C ℕ) (n : ℕ) (A : splitting_index_set [n]) :
  (Γ₀.splitting K).ι_summand A ≫ hom_app_f_f K n = hom_app_f_f_termwise K n A :=
(Γ₀.splitting K).ι_desc (op [n]) (hom_app_f_f_termwise K n) A

lemma ι_d_hom_app_eq_d (K : chain_complex C ℕ) (i j : ℕ) (hij : j+1 = i) :
  (Γ₀.splitting K).ι_summand (splitting_index_set.id [i]) ≫ K[Γ₀.obj K].d i j ≫
    hom_app_f_f K j = K.d i j :=
begin
  subst hij,
  simp only [hom_app_f_f, alternating_face_map_complex.obj_d_eq,
    preadditive.sum_comp, preadditive.comp_sum],
  rw finset.sum_eq_single (0 : fin (j+2)), rotate,
  { intros b h hb,
    simp only [preadditive.zsmul_comp, preadditive.comp_zsmul],
    erw [Γ₀.obj.map_mono_on_summand_id_assoc, (Γ₀.splitting K).ι_desc (op [j]),
      Γ₀.obj.termwise.map_mono_eq_zero, zero_comp, zsmul_zero],
    { intro hj,
      exact (nat.succ_ne_self j) (congr_arg simplex_category.len hj), },
    { simpa only [is_d₀.iff] using hb, }, },
  { intro h,
    exfalso,
    simpa only [finset.mem_univ, not_true] using h, },
  simp only [fin.coe_zero, pow_zero, one_zsmul],
  erw [Γ₀.obj.map_mono_on_summand_id_assoc, (Γ₀.splitting K).ι_desc (op [j]),
    hom_app_f_f_termwise_eq_id, comp_id, Γ₀.obj.termwise.map_mono_d₀' K],
end

lemma ι_d_hom_app_eq_zero (K : chain_complex C ℕ) (i j : ℕ) (hij : j+1=i)
  (A : splitting_index_set [i]) (hA : ¬A = splitting_index_set.id [i]) :
  (Γ₀.splitting K).ι_summand A ≫ K[Γ₀.obj K].d i j ≫ hom_app_f_f K j = 0 :=
begin
  subst hij,
  simp only [alternating_face_map_complex.obj_d_eq, preadditive.sum_comp, preadditive.comp_sum,
    preadditive.zsmul_comp, preadditive.comp_zsmul],
  by_cases hA' : A.1.len = j,
  { sorry, },
  { apply finset.sum_eq_zero,
    intros b h,
    erw [Γ₀.obj.map_on_summand'_assoc, Γ₀.obj.termwise.map_mono_eq_zero, zero_comp, zsmul_zero],
    sorry,
    sorry, },
end

@[simps]
def hom_app (K : chain_complex C ℕ) : (Γ₀ ⋙ N₁).obj K ⟶ (to_karoubi (chain_complex C ℕ)).obj K :=
{ f :=
  { f := λ n, hom_app_f_f K n,
    comm' := λ i j hij, begin
      apply (Γ₀.splitting K).hom_ext',
      intro A,
      by_cases A = splitting_index_set.id [i],
      { subst h,
        erw ι_d_hom_app_eq_d K i j hij,
        dsimp only [to_karoubi],
        simp only [ι_hom_app_f_f_assoc K, hom_app_f_f_termwise_eq_id, id_comp], },
      { erw ι_d_hom_app_eq_zero K i j hij A h,
        dsimp only [to_karoubi],
        simp only [ι_hom_app_f_f_assoc K i A, hom_app_f_f_termwise_eq_zero K i h, zero_comp], },
    end, },
  comm := begin
    ext n : 2,
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    dsimp,
    rw simplicial_object.splitting.ι_desc,
    by_cases A = splitting_index_set.id [n],
    { subst h,
      simp only [hom_app_f_f_termwise_eq_id, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
        simplicial_object.splitting.ι_desc _ (op [n]), comp_id], },
    { simp only [hom_app_f_f_termwise_eq_zero K n h, zero_comp,
        P_infty_on_Γ₀_splitting_summand_eq_zero_assoc K n h], },
  end, }

@[simps]
def hom : Γ₀ ⋙ N₁ ⟶ to_karoubi (chain_complex C ℕ) :=
{ app := hom_app,
  naturality' := λ K L f, begin
    ext n : 3,
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    dsimp,
    simp only [N₁_map_f, assoc, karoubi.comp, homological_complex.comp_f,
      alternating_face_map_complex.map_f, Γ₀.map_app, hom_app_f_f, hom_app_f_f_2,
      to_karoubi_map_f, simplicial_object.splitting.ι_desc_assoc],
    by_cases A = splitting_index_set.id [n],
    { subst h,
      sorry, },
    { sorry, },
  end }

@[simp]
def inv_app_f_f (K : chain_complex C ℕ) (n : ℕ) :
  K.X n ⟶ (Γ₀.obj K) _[n] :=
(Γ₀.splitting K).ι_summand (splitting_index_set.id [n])

@[simps]
def inv_app (K : chain_complex C ℕ) : (to_karoubi (chain_complex C ℕ)).obj K ⟶ (Γ₀ ⋙ N₁).obj K :=
{ f :=
  { f := λ n, inv_app_f_f K n,
    comm' := sorry, },
  comm := sorry, }

@[simps]
def inv : to_karoubi (chain_complex C ℕ) ⟶ Γ₀ ⋙ N₁ :=
{ app := inv_app,
  naturality' := sorry, }


/-

lemma simplex_category.eq_eq_to_hom_of_mono {x y : simplex_category} (i : x ⟶ y) [mono i] (hxy : x = y) :
  i = eq_to_hom hxy :=
begin
  unfreezingI { subst hxy, },
  exact simplex_category.eq_id_of_mono i,
end

lemma simplex_category.eq_eq_to_hom_of_epi {x y : simplex_category} (i : x ⟶ y) [epi i] (hxy : x = y) :
  i = eq_to_hom hxy :=
begin
  unfreezingI { subst hxy, },
  exact simplex_category.eq_id_of_epi i,
end

lemma d_on_KΓ' (K : chain_complex C ℕ) (j : ℕ) (A : splitting_index_set [j+1]) (hA : ¬A = splitting_index_set.id [j+1]) :
ι_Γ₀_summand K A ≫ K[Γ₀.obj K].d (j + 1) j ≫ sigma.desc (map_termwise K j) = 0 :=
begin
  erw chain_complex.of_d,
  dsimp,
  simp only [preadditive.sum_comp, preadditive.comp_sum, preadditive.zsmul_comp, preadditive.comp_zsmul, ← assoc],
  by_cases hA' : A.1.len = j, swap,
  { apply finset.sum_eq_zero,
    intros i hi,
    let θ := simplex_category.δ i ≫ A.e,
    erw [Γ₀.obj.map_on_summand' K A, assoc, colimit.ι_desc, cofan.mk_ι_app],
    erw [map_termwise_eq_zero, comp_zero, smul_zero'],
    { intro h,
      simp only at h,
      have hi' := simplex_category.len_le_of_mono (infer_instance : mono (image.ι θ)),
      erw splitting_index_set.eq_id_iff' at h,
      erw h at hi',
      cases nat.le.dest hi' with b hb,
      have he := simplex_category.len_le_of_epi (infer_instance : epi A.e),
      simp only [simplex_category.len_mk] at he hb,
      have hA'' : ¬A.1.len = j+1,
      { intro h,
        erw ← splitting_index_set.eq_id_iff' at h,
        exact hA h, },
      dsimp at he hb hA'',
      simp only [← hb, add_right_inj, add_le_add_iff_left] at hA'' he,
      have hb' := nat.lt_one_iff.mp ((ne.le_iff_lt hA'').mp he),
      rw [← hb, hb'] at hA',
      exact hA' rfl, }, },
  { have eq : A.1 = [j] := by { ext, exact hA', },
    haveI := epi_comp A.e (eq_to_hom eq),
    cases simplex_category.eq_σ_of_epi (A.e ≫ eq_to_hom eq : [j+1] ⟶ [j]) with i hi,
    let A' : splitting_index_set [j+1] := ⟨[j], ⟨simplex_category.σ i, by apply_instance⟩⟩,
    rw [splitting_index_set.ext A A' eq hi, fintype.sum_eq_add (fin.cast_succ i) i.succ], rotate,
    { by_contradiction,
      simpa only [fin.ext_iff, nat.one_ne_zero, fin.coe_succ, fin.coe_cast_succ, self_eq_add_right] using h, },
    { rintros k ⟨h₁, h₂⟩,
      convert zsmul_zero _,
      erw [Γ₀.obj.map_on_summand' K A', assoc, colimit.ι_desc, cofan.mk_ι_app],
      erw [map_termwise_eq_zero K, comp_zero],
      intro hj,
      dsimp at hj,
      rw splitting_index_set.eq_id_iff' at hj,
      have eq := image.fac (simplex_category.δ k ≫ A'.e),
      rw [simplex_category.eq_eq_to_hom_of_epi (factor_thru_image _) (by { ext, exact hj.symm, }),
        simplex_category.eq_eq_to_hom_of_mono (image.ι _) (by { ext, exact hj, }),
        eq_to_hom_trans, eq_to_hom_refl] at eq,
      have eq' := λ (l : fin ([j].len+1)), congr_arg (λ φ, (simplex_category.hom.to_order_hom φ) l) eq,
      simp only [simplex_category.hom.id, simplex_category.small_category_id,
        simplex_category.hom.to_order_hom_mk, order_hom.id_coe, id.def, simplex_category.hom.comp,
        simplex_category.small_category_comp, order_hom.comp_coe, function.comp_app] at eq',
      have ineqi := fin.is_lt i,
      by_cases (k : ℕ) < i,
      { let l : fin (j+1) := ⟨k, by linarith⟩,
        have hl := eq' l,
        erw fin.succ_above_above k l (by { rw [fin.le_iff_coe_le_coe,
          fin.cast_succ_mk, fin.eta], }) at hl,
        simp only [splitting_index_set.e] at hl,
        simp only [simplex_category.σ, simplex_category.hom.to_order_hom_mk,
          simplex_category.mk_hom, order_hom.coe_fun_mk] at hl,
        rw fin.pred_above_below i l.succ _ at hl, swap,
        { simp only [fin.succ_mk, nat.succ_eq_add_one, fin.coe_mk,
          fin.le_iff_coe_le_coe, fin.coe_cast_succ],
          linarith, },
        simp only [fin.ext_iff, fin.succ_mk, fin.coe_mk] at hl,
        rw fin.cast_pred_mk at hl, swap,
        { linarith, },
        simpa only [fin.coe_mk, self_eq_add_right] using hl, },
      { rw [not_lt] at h,
        let l : fin (j+1) := ⟨i+1, _⟩, swap,
        { simp only [add_lt_add_iff_right],
        by_contradiction h',
        simp only [not_lt] at h',
        have eqi : (i : ℕ) = j := ge_antisymm h' (nat.lt_succ_iff.mp ineqi),
        simp only [ne.def, fin.ext_iff, fin.coe_succ,
          fin.coe_cast_succ, eqi] at h₁ h₂,
        rw eqi at h,
        cases nat.le.dest h with c hc,
        have hk := nat.lt_succ_iff.mp (fin.is_lt k),
        rw ← hc at hk h₁ h₂,
        simp only [add_le_add_iff_left] at hk,
        cases eq_or_lt_of_le hk with hc' hc',
        { apply h₂,
          rw hc', },
        { apply h₁,
          simp only [nat.lt_one_iff] at hc',
          rw [hc', add_zero], }, },
        have hl := eq' l,
        erw fin.succ_above_below k l _ at hl, swap,
        { simp only [fin.lt_iff_coe_lt_coe, fin.cast_succ_mk, fin.coe_mk],
          by_contradiction hk,
          simp only [not_lt] at hk,
          simp only [ne.def, fin.ext_iff, fin.coe_succ,
            fin.coe_cast_succ] at h₁ h₂,
          cases nat.le.dest h with c hc,
          rw ← hc at hk h₁ h₂,
          simp only [add_right_eq_self, add_le_add_iff_left, add_right_inj] at h₁ h₂ hk,
          cases eq_or_lt_of_le hk with hc' hc',
          { exact h₂ hc', },
          { simp only [nat.lt_one_iff] at hc',
            exact h₁ hc', }, },
          rw [show fin.cast_succ l = i.succ, by { ext, simp only [fin.coe_succ, fin.cast_succ_mk, fin.coe_mk], }] at hl,
          simp only [splitting_index_set.e, simplex_category.σ, simplex_category.hom.to_order_hom_mk,
            simplex_category.mk_hom, order_hom.coe_fun_mk] at hl,
          rw fin.pred_above_above i i.succ _ at hl, swap,
          { simp only [fin.lt_iff_coe_lt_coe, lt_add_iff_pos_right,
              fin.coe_succ, fin.coe_cast_succ, nat.lt_one_iff], },
          simpa only [l, fin.pred_succ, fin.ext_iff, fin.coe_mk, nat.succ_ne_self] using hl, }, },
    { erw Γ₀.obj.map_on_summand K A' (show 𝟙 _ ≫ 𝟙 _ = simplex_category.δ (fin.cast_succ i) ≫
        simplex_category.σ i, by { rw [simplex_category.δ_comp_σ_self, id_comp], }),
      erw Γ₀.obj.map_on_summand K A' (show 𝟙 _ ≫ 𝟙 _ = simplex_category.δ i.succ ≫
        simplex_category.σ i, by { rw [simplex_category.δ_comp_σ_succ, id_comp], }),
      erw [Γ₀.obj.termwise.map_mono_id K, id_comp, ← add_zsmul],
      convert zero_zsmul _,
      simp only [fin.coe_cast_succ, fin.coe_succ, pow_succ, neg_mul, one_mul, add_right_neg], }, },
end-/

/-@[simps]
abbreviation hom : Γ₀ ⋙ N₁ ⟶ to_karoubi (chain_complex C ℕ) :=
{ app := λ K,
  { f :=
    { f:= λ n, sigma.desc (map_termwise K n),
      comm' := λ i j hij, begin
        have h : j+1 = i := hij,
        subst h,
        ext A,
        cases A,
        dsimp at A,
        simp only [cofan.mk_ι_app, colimit.ι_desc_assoc],
        by_cases A = splitting_index_set.id [j+1],
        { subst h,
          erw [d_on_KΓ K j, map_termwise_eq_id K, id_comp],
          refl, },
        { erw [d_on_KΓ' K j A h, map_termwise_eq_zero K h, zero_comp], },
      end },
    comm := begin
      ext n A,
      cases A,
      simp only [to_karoubi_obj_p, homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc],
      dsimp at ⊢ A,
      erw [comp_id],
      by_cases A = splitting_index_set.id [n],
      { subst h,
        simp only [ι_Γ₀_summand_id_comp_P_infty_assoc,
          map_termwise_eq_id, eq_to_hom_refl, colimit.ι_desc, cofan.mk_ι_app,
          simplex_category.len_mk, eq_self_iff_true, dite_eq_ite, if_true], },
      { rw [ι_Γ₀_summand_comp_P_infty_eq_zero_assoc K h, zero_comp, map_termwise_eq_zero K h], },
    end },
  naturality' := λ K L f, begin
    ext n A,
    cases A,
    dsimp at A,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, homological_complex.comp_f,
      alternating_face_map_complex.map, N₁_map_f, assoc, functor.comp_map, Γ₀_map, karoubi.comp,
      chain_complex.of_hom_f, to_karoubi_map_f, Γ₀.map_app],
    by_cases A = splitting_index_set.id [n],
    { subst h,
      dsimp,
      simp only [ι_Γ₀_summand_id_comp_P_infty_assoc, ι_colim_map_assoc, discrete.nat_trans_app,
        colimit.ι_desc, cofan.mk_ι_app, map_termwise_eq_id, id_comp],
      dsimp [splitting_index_set.id],
      rw comp_id, },
    { dsimp,
      rw [ι_Γ₀_summand_comp_P_infty_eq_zero_assoc K h, map_termwise_eq_zero K h,
        zero_comp, zero_comp], },
  end, }

@[simps]
abbreviation inv : to_karoubi (chain_complex C ℕ) ⟶ Γ₀ ⋙ N₁ :=
{ app := λ K,
  { f :=
    { f := λ n, sigma.ι (Γ₀.obj.summand K [n]) (splitting_index_set.id [n]),
      comm' := begin
        rintros i j (rfl : j+1 = i),
        erw [chain_complex.of_d, preadditive.comp_sum],
        erw finset.sum_eq_single (0 : fin (j+2)), rotate,
        { intros b hb hb',
          let i := simplex_category.δ b,
          rw [preadditive.comp_zsmul],
          erw Γ₀.obj.map_on_summand K (splitting_index_set.id [j+1]) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          rw [Γ₀.obj.termwise.map_mono_eq_zero K i, zero_comp, zsmul_zero],
          { intro h,
            exact nat.succ_ne_self j (congr_arg simplex_category.len h), },
          { rw is_d₀.iff, exact hb', }, },
        { simp only [finset.mem_univ, not_true, is_empty.forall_iff], },
        { simp only [fin.coe_zero, pow_zero, one_zsmul],
          let i := simplex_category.δ (0 : fin (j+2)),
          erw Γ₀.obj.map_on_summand K (splitting_index_set.id [j+1]) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          congr',
          apply Γ₀.obj.termwise.map_mono_d₀ K i,
          erw is_d₀.iff, },
      end },
    comm := begin
      ext n,
      dsimp,
      simp only [ι_Γ₀_summand_id_comp_P_infty, discrete.nat_trans_app, ι_colim_map, id_comp],
    end },
  naturality' := λ K L f, begin
    ext n,
    simp only [karoubi.comp, homological_complex.comp_f],
    dsimp,
    simpa only [ι_Γ₀_summand_id_comp_P_infty_assoc, ι_colim_map, discrete.nat_trans_app],
  end }-/

end N₁Γ₀

@[simps]
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ) :=
{ hom := N₁Γ₀.hom,
  inv := N₁Γ₀.inv,
  hom_inv_id' := begin
    ext K n : 5,
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    dsimp at A,
    simp only [nat_trans.comp_app, N₁Γ₀.hom_app_2, N₁Γ₀.inv_app_2,
      karoubi.comp, homological_complex.comp_f, N₁Γ₀.hom_app_f_f,
      N₁Γ₀.hom_app_f_f_2, N₁Γ₀.inv_app_f_f, N₁Γ₀.inv_app_f_f_2,
      nat_trans.id_app, karoubi.id_eq, (Γ₀.splitting K).ι_desc_assoc (op [n])],
    by_cases A = splitting_index_set.id [n],
    { subst h,
      dsimp,
      simpa only [N₁Γ₀.hom_app_f_f_termwise_eq_id,
        P_infty_on_Γ₀_splitting_summand_eq_self] using id_comp _, },
    { dsimp,
      simp only [N₁Γ₀.hom_app_f_f_termwise_eq_zero K n h,
        P_infty_on_Γ₀_splitting_summand_eq_zero K n h, zero_comp], },
  end,
  inv_hom_id' := begin
    ext K n,
    simpa only [nat_trans.comp_app, N₁Γ₀.inv_app_2, N₁Γ₀.hom_app_2,
      karoubi.comp, homological_complex.comp_f, N₁Γ₀.inv_app_f_f,
      N₁Γ₀.inv_app_f_f_2, N₁Γ₀.hom_app_f_f, N₁Γ₀.hom_app_f_f_2, to_karoubi_obj_p,
      nat_trans.id_app, karoubi.id_eq, (Γ₀.splitting K).ι_desc (op [n]),
      N₁Γ₀.hom_app_f_f_termwise_eq_id],
  end, }

def N₂Γ₂_to_karoubi : to_karoubi (chain_complex C ℕ) ⋙ Γ₂ ⋙ N₂ = Γ₀ ⋙ N₁ :=
begin
  have h := functor.congr_obj (functor_extension₂_comp_whiskering_left_to_karoubi (chain_complex C ℕ) (simplicial_object C)) Γ₀,
  have h' := functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi (simplicial_object C) (chain_complex C ℕ)) N₁,
  dsimp at h h',
  erw [← functor.assoc_eq, h, functor.assoc_eq, h'],
end

@[simps]
def N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ)) :=
(whiskering_left_to_karoubi_iso_equiv (Γ₂ ⋙ N₂) (𝟭 (karoubi (chain_complex C ℕ)))).inv_fun
((eq_to_iso N₂Γ₂_to_karoubi).trans N₁Γ₀)

lemma N₂Γ₂_compatible_with_N₁Γ₀ (K: chain_complex C ℕ) :
  N₂Γ₂.hom.app ((to_karoubi _).obj K) = eq_to_hom (by { exact functor.congr_obj N₂Γ₂_to_karoubi K, })
    ≫ N₁Γ₀.hom.app K :=
begin
  dsimp only [N₂Γ₂, N₁Γ₀, whiskering_left_to_karoubi_iso_equiv],
  erw [whiskering_left_to_karoubi_hom_equiv_inv_fun_compat],
  dsimp only [iso.trans, eq_to_iso],
  simp only [nat_trans.comp_app, eq_to_hom_app],
end

end dold_kan

end algebraic_topology
