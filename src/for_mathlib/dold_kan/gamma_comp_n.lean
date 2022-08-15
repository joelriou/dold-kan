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
  (K : chain_complex C ℕ) (n : ℕ) {A : simplex_category.splitting_index_set (op [n])}
  (hA : ¬ A.eq_id) :
  (Γ₀.splitting K).ι_summand A ≫ (P_infty : K[Γ₀.obj K] ⟶ _).f n = 0 :=
P_infty_on_splitting_eq_zero (Γ₀.splitting K) A hA

def higher_faces_vanish.on_Γ₀_summand_id (K : chain_complex C ℕ) (n : ℕ) :
  higher_faces_vanish (n+1) ((Γ₀.splitting K).ι_summand (splitting_index_set.id (op [n+1]))) :=
begin
  intros j hj,
  have eq := Γ₀.obj.map_mono_on_summand_id K (simplex_category.δ j.succ),
  rw [Γ₀.obj.termwise.map_mono_eq_zero K, zero_comp] at eq, rotate,
  { intro h,
    exact (nat.succ_ne_self n) (congr_arg simplex_category.len h), },
  { intro h,
    simp only [is_d₀.iff] at h,
    exact fin.succ_ne_zero j h, },
  exact eq,
end

@[simp, reassoc]
lemma P_infty_on_Γ₀_splitting_summand_eq_self
  (K : chain_complex C ℕ) {n : ℕ} :
  (Γ₀.splitting K).ι_summand (simplex_category.splitting_index_set.id (op [n])) ≫ (P_infty : K[Γ₀.obj K] ⟶ _).f n =
    (Γ₀.splitting K).ι_summand (simplex_category.splitting_index_set.id (op [n])) :=
begin
  rw P_infty_f,
  cases n,
  { simpa only [P_f_0_eq] using comp_id _, },
  { exact (higher_faces_vanish.on_Γ₀_summand_id K n).comp_P_eq_self, },
end

namespace N₁Γ₀

def hom_app_f_f_termwise (K : chain_complex C ℕ) (n : ℕ) (A : splitting_index_set (op [n])) :
  Γ₀.obj.summand K (op [n]) A ⟶ K.X n :=
begin
  by_cases A.eq_id,
  { dsimp at h,
    subst h,
    exact 𝟙 _, },
  { exact 0, }
end

@[simp]
lemma hom_app_f_f_termwise_eq_id (K : chain_complex C ℕ) (n : ℕ) :
hom_app_f_f_termwise K n (splitting_index_set.id (op [n])) = 𝟙 _ :=
begin
  dsimp [hom_app_f_f_termwise],
  simp only [eq_self_iff_true, if_true],
end

lemma hom_app_f_f_termwise_eq_zero (K : chain_complex C ℕ) (n : ℕ)
  {A : splitting_index_set (op [n])} (h : ¬ A.eq_id) :
hom_app_f_f_termwise K n A = 0 :=
begin
  dsimp [hom_app_f_f_termwise],
  rw dif_neg,
  exact h,
end

@[simp]
def hom_app_f_f (K : chain_complex C ℕ) (n : ℕ) :
  (Γ₀.obj K) _[n] ⟶ K.X n :=
(Γ₀.splitting K).desc (op [n]) (hom_app_f_f_termwise K n)

@[simp, reassoc]
lemma ι_hom_app_f_f (K : chain_complex C ℕ) (n : ℕ) (A : splitting_index_set (op [n])) :
  (Γ₀.splitting K).ι_summand A ≫ hom_app_f_f K n = hom_app_f_f_termwise K n A :=
(Γ₀.splitting K).ι_desc (op [n]) (hom_app_f_f_termwise K n) A

@[reassoc]
lemma ι_id_d (K : chain_complex C ℕ) (i j : ℕ) (hij : j+1 = i) :
  (Γ₀.splitting K).ι_summand (splitting_index_set.id (op [i])) ≫
    ((Γ₀ ⋙ N₁).obj K).X.d i j = --K[Γ₀.obj K].d i j =
  K.d i j ≫ (Γ₀.splitting K).ι_summand (splitting_index_set.id (op [j])) :=
begin
  subst hij,
  dsimp,
  simp only [alternating_face_map_complex.obj_d_eq, preadditive.comp_sum],
  rw finset.sum_eq_single (0 : fin (j+2)), rotate,
  { intros b h hb,
    erw [preadditive.comp_zsmul, Γ₀.obj.map_mono_on_summand_id,
      Γ₀.obj.termwise.map_mono_eq_zero, zero_comp, zsmul_zero],
    { intro hj,
      exact (nat.succ_ne_self j) (congr_arg simplex_category.len hj), },
    { simpa only [is_d₀.iff] using hb, }, },
  { intro h,
    exfalso,
    simpa only [finset.mem_univ, not_true] using h, },
  erw [fin.coe_zero, pow_zero, one_zsmul,
    Γ₀.obj.map_mono_on_summand_id K (simplex_category.δ (0 : fin (j+2))),
    Γ₀.obj.termwise.map_mono_d₀'],
end

lemma ι_d_hom_app_eq_zero.term_is_zero (K : chain_complex C ℕ) (j : ℕ)
  {A : splitting_index_set (op [j+1])} (hA : ¬ A.eq_id) (b : fin (j+2))
  (hb : ¬ is_iso (simplex_category.δ b ≫ A.e)):
  (-1 : ℤ) ^ (b : ℕ) • (Γ₀.splitting K).ι_summand A ≫
    (Γ₀.obj K).δ b ≫ hom_app_f_f K j = 0 :=
begin
  erw Γ₀.obj.map_on_summand'_assoc K A (simplex_category.δ b).op,
  simp only [hom_app_f_f, (Γ₀.splitting K).ι_desc],
  dsimp only [splitting_index_set.pull],
--  δ b ≫ A.e
-- |j] ⟶ [j+1] ⟶ A.e
-- pour que ce soit difféent de zéro, il faut :
--  - soit A.e = id et b =0 [on a fait l'hypothèse A.e ≠ id]
--  - que le composé soit un iso
-- pour que ce soit égal à zéro,
-- il suffit : (A.e ≠ id ou b ≠ 0 )
  sorry
end

lemma fin.is_succ_of_ne_zero {j : ℕ} (x : fin (j+1)) (hx : x ≠ 0) :
  ∃ (y : fin j), x = y.succ :=
⟨x.pred hx, (fin.succ_pred _ _).symm⟩

lemma ι_d_hom_app_eq_zero (K : chain_complex C ℕ) (i j : ℕ) (hij : j+1=i)
  {A : splitting_index_set (op [i])} (hA : ¬ A.eq_id) :
  (Γ₀.splitting K).ι_summand A ≫ ((Γ₀ ⋙ N₁).obj K).X.d i j ≫ hom_app_f_f K j = 0 :=
begin
  subst hij,
  dsimp only [functor.comp_obj, N₁],
  simp only [alternating_face_map_complex.obj_d_eq, preadditive.sum_comp,
    preadditive.comp_sum, preadditive.zsmul_comp, preadditive.comp_zsmul],
  by_cases hA' : A.1.unop.len = j,
  { rcases A with ⟨Δ, e, he⟩,
    induction Δ using opposite.rec,
    induction Δ using simplex_category.rec with k,
    dsimp at hA',
    subst hA',
    haveI := he,
    cases simplex_category.eq_σ_of_epi e with i hi,
    unfreezingI { subst hi, },
    rw fintype.sum_eq_add (fin.cast_succ i) i.succ, rotate,
    { intro h,
      simpa only [fin.ext_iff, fin.coe_cast_succ, fin.coe_succ,
        self_eq_add_right, nat.one_ne_zero] using h, },
    { intros b hb,
      apply ι_d_hom_app_eq_zero.term_is_zero K k hA,
      intro h,
      change is_iso (simplex_category.δ b ≫ simplex_category.σ i) at h,
      by_cases hbi : (b : ℕ)<i,
      { have hi : i ≠ 0,
        { intro hi,
          simpa only [fin.coe_zero, not_lt_zero', hi] using hbi, },
        cases fin.is_succ_of_ne_zero i hi with j hj,
        unfreezingI { subst hj, cases k, fin_cases j, },
        let b' := fin.cast_pred b,
        have hb' : b'.cast_succ = b,
        { apply fin.cast_succ_cast_pred,
          rw fin.lt_iff_coe_lt_coe,
          apply hbi.trans,
          simpa only [fin.coe_succ, fin.coe_last, add_lt_add_iff_right] using j.is_lt, },
        have hbi' : b' ≤ j.cast_succ,
        { dsimp [b'],
          simp only [← hb', fin.le_iff_coe_le_coe, fin.cast_pred_cast_succ, fin.coe_cast_succ,
            ← nat.lt_succ_iff],
          simpa only [← hb', fin.coe_succ] using hbi, },
        have eq := simplex_category.δ_comp_σ_of_le hbi',
        rw hb' at eq,
        rw eq at h,
        haveI := h,
        have h' := len_le_of_epi (epi_of_epi (σ j) (δ b')),
        dsimp at h',
        simpa only [add_le_iff_nonpos_right, le_zero_iff] using h', },
      { simp only [not_lt] at hbi,
        have hbi' : (i : ℕ)+2 ≤ b,
        { cases nat.le.dest hbi with t ht,
          suffices : 2 ≤ t,
          { linarith, },
          by_contra' ht' : _,
          let t' : fin 2 := ⟨t, ht'⟩,
          fin_cases t',
          { apply hb.1,
            symmetry,
            simp only [t', fin.ext_iff, fin.coe_mk, fin.coe_zero] at this,
            simpa only [this, add_zero, fin.ext_iff] using ht, },
          { apply hb.2,
            symmetry,
            simp only [fin.ext_iff, fin.coe_mk, fin.coe_one] at this,
            simpa only [this, fin.ext_iff, fin.coe_succ] using ht, }, },
        have hb : b ≠ 0,
        { intro hb,
          rw hb at hbi',
          simpa only [fin.coe_zero, le_zero_iff] using hbi', },
        cases fin.is_succ_of_ne_zero b hb with b' hb',
        unfreezingI { cases k, fin_cases i, },
        { simpa only [fin.coe_fin_one, lt_self_iff_false]
            using lt_of_le_of_lt hbi' (b.is_lt), },
        let i' := i.cast_pred,
        have hi' : i'.cast_succ = i,
        { apply fin.cast_succ_cast_pred,
          rw [fin.lt_iff_coe_lt_coe, ← nat.succ_le_iff, ← nat.succ_le_succ_iff],
          refine le_trans hbi' _,
          simpa only [← nat.lt_succ_iff] using b.is_lt, },
        rw [hb', ← hi'] at h,
        have hbi'' : i'.cast_succ < b',
        { rw [hi', fin.lt_iff_coe_lt_coe, ← nat.succ_lt_succ_iff, ← nat.succ_le_iff],
          simpa only [hb', fin.coe_succ] using hbi', },
        rw simplex_category.δ_comp_σ_of_gt hbi'' at h,
        haveI := h,
        have h' := len_le_of_epi (epi_of_epi (σ i') (δ b')),
        simpa only [len_mk, add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using h', }, },
    { let A : splitting_index_set (op [k+1]) := ⟨op [k], ⟨σ i, he⟩⟩,
      erw [Γ₀.obj.map_on_summand_assoc K A
        (simplex_category.δ i.succ).op (_ : 𝟙 _ ≫ 𝟙 _ = _),
        Γ₀.obj.map_on_summand_assoc K A
        (simplex_category.δ (fin.cast_succ i)).op (_ : 𝟙 _ ≫ 𝟙 _ = _),
        fin.coe_cast_succ, fin.coe_succ, pow_succ, neg_mul, one_mul, neg_smul, add_right_neg];
      symmetry; rw [id_comp, quiver.hom.unop_op],
      exacts [δ_comp_σ_self, δ_comp_σ_succ], }, },
  { rw finset.sum_eq_zero,
    intros b h,
    apply ι_d_hom_app_eq_zero.term_is_zero K j hA b,
    introI hb,
    simp only [splitting_index_set.eq_id_iff_len_le, unop_op, len_mk, not_le] at hA,
    have hA'' : j < _ := lt_of_le_of_ne (len_le_of_mono (infer_instance : mono (δ b ≫ A.e)))
      (ne_comm.mp hA'),
    rw ← nat.succ_le_iff at hA'',
    simpa only [lt_self_iff_false] using lt_of_le_of_lt hA'' hA, },
end

@[simps]
def hom_app (K : chain_complex C ℕ) : (Γ₀ ⋙ N₁).obj K ⟶ (to_karoubi (chain_complex C ℕ)).obj K :=
{ f :=
  { f := λ n, hom_app_f_f K n,
    comm' := λ i j hij, begin
      apply (Γ₀.splitting K).hom_ext',
      intro A,
      by_cases A.eq_id,
      { dsimp at h,
        subst h,
        simp only [ι_id_d_assoc K i j hij, hom_app_f_f, (Γ₀.splitting K).ι_desc,
          (Γ₀.splitting K).ι_desc_assoc, hom_app_f_f_termwise_eq_id],
        dsimp,
        erw [id_comp, comp_id], },
      { rw [ι_d_hom_app_eq_zero K i j hij h, hom_app_f_f,
          (Γ₀.splitting K).ι_desc_assoc, hom_app_f_f_termwise_eq_zero K i h,
          zero_comp], },
    end, },
  comm := begin
    ext n : 2,
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    dsimp,
    rw simplicial_object.splitting.ι_desc,
    by_cases A.eq_id,
    { dsimp at h,
      subst h,
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
    by_cases A.eq_id,
    { dsimp at h,
      subst h,
      rw P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
      simp only [(Γ₀.splitting K).ι_desc_assoc, assoc, (Γ₀.splitting L).ι_desc,
        hom_app_f_f_termwise_eq_id],
      dsimp [splitting_index_set.id],
      erw [comp_id, id_comp], },
    { simp only [P_infty_on_Γ₀_splitting_summand_eq_zero_assoc K n h,
        hom_app_f_f_termwise_eq_zero K n h, zero_comp], },
  end }

@[simp]
def inv_app_f_f (K : chain_complex C ℕ) (n : ℕ) :
  K.X n ⟶ (Γ₀.obj K) _[n] :=
(Γ₀.splitting K).ι_summand (splitting_index_set.id (op [n]))

@[simps]
def inv_app (K : chain_complex C ℕ) : (to_karoubi (chain_complex C ℕ)).obj K ⟶ (Γ₀ ⋙ N₁).obj K :=
{ f :=
  { f := λ n, inv_app_f_f K n,
    comm' := λ i j hij, ι_id_d K i j hij, },
  comm := by tidy, }

@[simps]
def inv : to_karoubi (chain_complex C ℕ) ⟶ Γ₀ ⋙ N₁ :=
{ app := inv_app,
  naturality' := λ X Y f, begin
    ext n : 3,
    dsimp,
    simpa only [to_karoubi_map_f, karoubi.comp, homological_complex.comp_f,
      inv_app_f_f, inv_app_f_f_2, N₁_map_f, alternating_face_map_complex.map_f,
      Γ₀.map_app, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
      (Γ₀.splitting X).ι_desc (op [n])],
  end, }

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
  end, }-/


end N₁Γ₀

@[simps]
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ) :=
{ hom := N₁Γ₀.hom,
  inv := N₁Γ₀.inv,
  hom_inv_id' := begin
    ext K n : 5,
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    simp only [nat_trans.comp_app, N₁Γ₀.hom_app_2, N₁Γ₀.inv_app_2,
      karoubi.comp, homological_complex.comp_f, N₁Γ₀.hom_app_f_f,
      N₁Γ₀.hom_app_f_f_2, N₁Γ₀.inv_app_f_f, N₁Γ₀.inv_app_f_f_2,
      nat_trans.id_app, karoubi.id_eq, (Γ₀.splitting K).ι_desc_assoc (op [n])],
    by_cases A.eq_id,
    { dsimp at h,
      subst h,
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
