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
--open opposite
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]

namespace N₁Γ₀

def map_termwise (K : chain_complex C ℕ) (n : ℕ) (A : Γ_index_set [n]) :
Γ₀.obj.summand K [n] A ⟶ ((to_karoubi (chain_complex C ℕ)).obj K).X.X n :=
begin
  by_cases A = Γ_index_set.id [n],
  { subst h,
    exact 𝟙 _, },
  { exact 0, }
end

lemma map_termwise_eq_id (K : chain_complex C ℕ) (n : ℕ) :
map_termwise K n (Γ_index_set.id [n]) = 𝟙 _ :=
begin
  dsimp [map_termwise],
  simp only [eq_self_iff_true, if_true],
end

lemma map_termwise_eq_zero (K : chain_complex C ℕ) {n : ℕ} {A : Γ_index_set [n]}
  (h : ¬ A = Γ_index_set.id [n]) :
map_termwise K n A = 0 :=
begin
  dsimp [map_termwise],
  split_ifs,
  refl,
end

lemma d_on_KΓ (K : chain_complex C ℕ) (j : ℕ) :
  ι_Γ₀_summand K (Γ_index_set.id [j+1]) ≫ K[Γ₀.obj K].d (j+1) j
    ≫ sigma.desc (map_termwise K j) = K.d (j+1) j :=
begin
  erw chain_complex.of_d,
  dsimp,
  simp only [preadditive.sum_comp, preadditive.comp_sum, preadditive.zsmul_comp, preadditive.comp_zsmul, ← assoc],
  erw finset.sum_eq_single (0 : fin (j+2)), rotate,
  { intros b hb₀ hb,
    let i := simplex_category.δ b,
    erw Γ₀.obj.map_on_summand K (Γ_index_set.id [j+1])
      (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
    erw Γ₀.obj.termwise.map_mono_eq_zero K i (λ hj, by simpa only [simplex_category.len_mk, nat.succ_ne_self]
      using congr_arg simplex_category.len hj) (by { rw is_d₀.iff, exact hb, }),
    simp only [smul_zero', zero_comp], },
  { intro h, exfalso, simpa only [finset.mem_univ, not_true] using h, },
  { simp only [fin.coe_zero, pow_zero, ← assoc, one_zsmul],
    let i := simplex_category.δ (0 : fin (j+2)),
    erw Γ₀.obj.map_on_summand K (Γ_index_set.id [j+1])
      (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
    erw [Γ₀.obj.termwise.map_mono_d₀ K i (is_d₀.iff.mpr rfl), assoc],
    simp only [colimit.ι_desc, cofan.mk_ι_app],
    erw [map_termwise_eq_id, comp_id],
    refl, },
end

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

lemma d_on_KΓ' (K : chain_complex C ℕ) (j : ℕ) (A : Γ_index_set [j+1]) (hA : ¬A = Γ_index_set.id [j+1]) :
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
      erw Γ_index_set.eq_id_iff' at h,
      erw h at hi',
      cases nat.le.dest hi' with b hb,
      have he := simplex_category.len_le_of_epi (infer_instance : epi A.e),
      simp only [simplex_category.len_mk] at he hb,
      have hA'' : ¬A.1.len = j+1,
      { intro h,
        erw ← Γ_index_set.eq_id_iff' at h,
        exact hA h, },
      dsimp at he hb hA'',
      simp only [← hb, add_right_inj, add_le_add_iff_left] at hA'' he,
      have hb' := nat.lt_one_iff.mp ((ne.le_iff_lt hA'').mp he),
      rw [← hb, hb'] at hA',
      exact hA' rfl, }, },
  { have eq : A.1 = [j] := by { ext, exact hA', },
    haveI := epi_comp A.e (eq_to_hom eq),
    cases simplex_category.eq_σ_of_epi (A.e ≫ eq_to_hom eq : [j+1] ⟶ [j]) with i hi,
    let A' : Γ_index_set [j+1] := ⟨[j], ⟨simplex_category.σ i, by apply_instance⟩⟩,
    rw [Γ_index_set.ext A A' eq hi, fintype.sum_eq_add (fin.cast_succ i) i.succ], rotate,
    { by_contradiction,
      simpa only [fin.ext_iff, nat.one_ne_zero, fin.coe_succ, fin.coe_cast_succ, self_eq_add_right] using h, },
    { rintros k ⟨h₁, h₂⟩,
      convert zsmul_zero _,
      erw [Γ₀.obj.map_on_summand' K A', assoc, colimit.ι_desc, cofan.mk_ι_app],
      erw [map_termwise_eq_zero K, comp_zero],
      intro hj,
      dsimp at hj,
      rw Γ_index_set.eq_id_iff' at hj,
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
        simp only [Γ_index_set.e] at hl,
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
          simp only [Γ_index_set.e, simplex_category.σ, simplex_category.hom.to_order_hom_mk,
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
end

@[simps]
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
        by_cases A = Γ_index_set.id [j+1],
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
      by_cases A = Γ_index_set.id [n],
      { subst h,
        simp only [P_infty_eq_id_on_Γ₀_summand_assoc,
          map_termwise_eq_id, eq_to_hom_refl, colimit.ι_desc, cofan.mk_ι_app,
          simplex_category.len_mk, eq_self_iff_true, dite_eq_ite, if_true], },
      { rw [P_infty_eq_zero_on_Γ₀_summand_assoc K h, zero_comp, map_termwise_eq_zero K h], },
    end },
  naturality' := λ K L f, begin
    ext n A,
    cases A,
    dsimp at A,
    simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, homological_complex.comp_f,
      alternating_face_map_complex.map, N₁_map_f, assoc, functor.comp_map, Γ₀_map, karoubi.comp,
      chain_complex.of_hom_f, to_karoubi_map_f, Γ₀.map_app],
    by_cases A = Γ_index_set.id [n],
    { subst h,
      dsimp,
      simp only [P_infty_eq_id_on_Γ₀_summand_assoc, ι_colim_map_assoc, discrete.nat_trans_app,
        colimit.ι_desc, cofan.mk_ι_app, map_termwise_eq_id],
      erw [id_comp, comp_id],
      refl, },
    { dsimp,
      rw [P_infty_eq_zero_on_Γ₀_summand_assoc K h, map_termwise_eq_zero K h,
        zero_comp, zero_comp], },
  end, }

@[simps]
abbreviation inv : to_karoubi (chain_complex C ℕ) ⟶ Γ₀ ⋙ N₁ :=
{ app := λ K,
  { f :=
    { f := λ n, sigma.ι (Γ₀.obj.summand K [n]) (Γ_index_set.id [n]),
      comm' := λ i j hij, begin
        have h : j+1 = i := hij,
        subst h,
        erw [chain_complex.of_d, preadditive.comp_sum],
        erw finset.sum_eq_single (0 : fin (j+2)), rotate,
        { intros b hb hb',
          let i := simplex_category.δ b,
          rw [preadditive.comp_zsmul],
          erw Γ₀.obj.map_on_summand K (Γ_index_set.id [j+1]) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          rw [Γ₀.obj.termwise.map_mono_eq_zero K i, zero_comp, zsmul_zero],
          { intro h,
            exact nat.succ_ne_self j (congr_arg simplex_category.len h), },
          { rw is_d₀.iff, exact hb', }, },
        { simp only [finset.mem_univ, not_true, forall_false_left], },
        { simp only [fin.coe_zero, pow_zero, one_zsmul],
          let i := simplex_category.δ (0 : fin (j+2)),
          erw Γ₀.obj.map_on_summand K (Γ_index_set.id [j+1]) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          congr',
          apply Γ₀.obj.termwise.map_mono_d₀ K i,
          erw is_d₀.iff, },
      end },
    comm := begin
      ext n,
      dsimp,
      slice_rhs 2 3 { erw P_infty_eq_id_on_Γ₀_summand, },
      simp only [discrete.nat_trans_app, ι_colim_map, id_comp],
    end },
  naturality' := λ K L f, begin
    ext n,
    simp only [karoubi.comp, homological_complex.comp_f],
    erw [← assoc, P_infty_eq_id_on_Γ₀_summand, ι_colim_map, discrete.nat_trans_app],
    refl,
  end }

end N₁Γ₀

@[simps]
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ) :=
{ hom := N₁Γ₀.hom,
  inv := N₁Γ₀.inv,
  hom_inv_id' := begin
    ext K n A,
    cases A,
    simp only [homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc_assoc,
      nat_trans.id_app, karoubi.id_eq, karoubi.comp, nat_trans.comp_app],
    dsimp at ⊢ A,
    by_cases A = Γ_index_set.id [n],
    { subst h,
      simp only [P_infty_eq_id_on_Γ₀_summand, N₁Γ₀.map_termwise_eq_id, id_comp], },
    { simp only [P_infty_eq_zero_on_Γ₀_summand K h, N₁Γ₀.map_termwise_eq_zero K h, zero_comp], },
  end,
  inv_hom_id' := begin
    ext K n,
    dsimp,
    simpa only [karoubi.comp, homological_complex.comp_f, colimit.ι_desc, cofan.mk_ι_app,
      N₁Γ₀.map_termwise_eq_id],
  end }

def N₂Γ₂_to_karoubi : to_karoubi (chain_complex C ℕ) ⋙ Γ₂ ⋙ N₂ = Γ₀ ⋙ N₁ :=
begin
  have h := congr_obj (functor_extension''_comp_whiskering_left_to_karoubi (chain_complex C ℕ) (simplicial_object C)) Γ₀,
  have h' := congr_obj (functor_extension'_comp_whiskering_left_to_karoubi (simplicial_object C) (chain_complex C ℕ)) N₁,
  dsimp at h h',
  erw [← functor.assoc, h, functor.assoc, h'],
end

@[simps]
def N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ)) :=
(whiskering_left_to_karoubi_iso_equiv (Γ₂ ⋙ N₂) (𝟭 (karoubi (chain_complex C ℕ)))).inv_fun
((eq_to_iso N₂Γ₂_to_karoubi).trans N₁Γ₀)

lemma N₂Γ₂_compatible_with_N₁Γ₀ (K: chain_complex C ℕ) :
  N₂Γ₂.hom.app ((to_karoubi _).obj K) = eq_to_hom (by { exact congr_obj N₂Γ₂_to_karoubi K, })
    ≫ N₁Γ₀.hom.app K :=
begin
  dsimp only [N₂Γ₂, N₁Γ₀, whiskering_left_to_karoubi_iso_equiv],
  erw [whiskering_left_to_karoubi_hom_equiv_inv_fun_compat],
  dsimp only [iso.trans, eq_to_iso],
  simp only [nat_trans.comp_app, eq_to_hom_app],
end

end dold_kan

end algebraic_topology
