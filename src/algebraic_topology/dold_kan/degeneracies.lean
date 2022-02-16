/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.decomposition
import algebraic_topology.dold_kan.functor_gamma
import algebraic_topology.dold_kan.functor_n

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open opposite
open_locale simplicial

noncomputable theory

universe v

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category.{v} C] [additive_category C]

lemma P_infty_eq_id_on_Γ_summand (K : chain_complex C ℕ) (n : ℕ) :
  inclusion_Γ_summand K (Γ_index_id n) ≫ P_infty.f n =
    inclusion_Γ_summand K (Γ_index_id n) :=
begin
  rw P_infty_degreewise,
  cases n,
  { erw [P_deg0_eq, comp_id], },
  { apply P_is_identity_where_faces_vanish,
    refine ⟨_⟩,
    intros j hj,
    let i := simplex_category.δ j.succ,
    erw Γ_simplicial_on_summand K (Γ_index_id (n+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
    rw [Γ_on_mono_eq_zero K i _ _, zero_comp],
    { intro h, 
      apply nat.succ_ne_self n,
      simpa only [simplex_category.len_mk] using congr_arg simplex_category.len h, },
    { rintro ⟨h₁, h₂⟩,
      erw fin.succ_above_below j.succ 0 (fin.succ_pos j) at h₂,
      exact h₂ rfl, }, },
end

lemma inclusion_Γ_summand_decomp (K : chain_complex C ℕ)
  {Δ Δ' : simplex_category.{v}} (e : Δ ⟶ Δ') [epi e] :
  sigma.ι (Γ_summand K Δ') ⟨Δ', ⟨𝟙 _, by apply_instance⟩⟩ ≫ Γ_simplicial K e =
  sigma.ι (Γ_summand K Δ) ⟨Δ', ⟨e, by apply_instance⟩⟩ :=
begin
  erw Γ_simplicial_on_summand K ⟨Δ', ⟨𝟙 _, by apply_instance⟩⟩
    (show e ≫ 𝟙 _ = e ≫ 𝟙 _, by refl),
  erw [Γ_on_mono_on_id K (𝟙 Δ') rfl, eq_to_hom_refl, id_comp],
end

lemma higher_faces_vanish_σφ {Y : C} {X : simplicial_object C} {n b q : ℕ} (hnbq : n+1=b+q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : higher_faces_vanish q (φ ≫ X.σ ⟨b,
    by { rw [hnbq, nat.lt_succ_iff, le_add_iff_nonneg_right], exact zero_le q, }⟩) :=
{ vanishing := λ j hj, begin
    rw assoc,
    have eq := simplicial_object.δ_comp_σ_of_gt X (_ : fin.cast_succ ⟨b, _⟩ < j), rotate,
    { rw [hnbq, lt_add_iff_pos_right],
      by_contradiction,
      simp only [not_lt, nonpos_iff_eq_zero] at h,
      rw [h, add_zero] at hj,
      exact (lt_self_iff_false _).mp (lt_of_le_of_lt hj (fin.is_lt j)), },
    { rw [fin.cast_succ_mk, fin.lt_iff_coe_lt_coe, fin.coe_mk, nat.lt_iff_add_one_le,
        ← add_le_add_iff_right q, add_assoc, add_comm 1, ← add_assoc, ← hnbq],
      exact hj, },
    simp only [fin.cast_succ_mk] at eq,
    erw [eq, ← assoc],
    have eq' := v.vanishing (j.pred _) _, rotate,
    { intro hj',
      rw [hj', hnbq] at hj,
      simpa only [fin.coe_zero, zero_add, add_comm b, add_assoc,
        nat.one_ne_zero, add_le_iff_nonpos_right, add_eq_zero_iff, nonpos_iff_eq_zero, false_and] using hj, },
    { rw [← add_le_add_iff_right 1, add_assoc _ q, add_comm q 1, ← add_assoc,
        ← fin.coe_succ, fin.succ_pred],
      exact hj, },
    simp only [fin.succ_pred] at eq',
    rw [eq', zero_comp],
  end }

lemma P_q_eq_zero_on_σ (X : simplicial_object C)
  {n q : ℕ} : ∀ (i : fin (n+1)) (hi : (n+1) ≤ (i : ℕ)+q),
  (X.σ i) ≫ (P q).f (n+1) = 0 :=
begin
  induction q with q hq,
  { intros i hi,
    exfalso,
    have h := fin.is_lt i,
    linarith, },
  { intros i hi,
    by_cases n+1 ≤ (i : ℕ)+q,
    { unfold P,
      simp only [homological_complex.comp_f, ← assoc],
      rw [hq i h, zero_comp], },
    { have hi' : n = (i : ℕ) + q,
      { cases le_iff_exists_add.mp hi with j hj,
        rw [← nat.lt_succ_iff, nat.succ_eq_add_one, add_assoc, hj, not_lt, add_le_iff_nonpos_right,
          nonpos_iff_eq_zero] at h,
        rw [← add_left_inj 1, add_assoc, hj, self_eq_add_right, h], },
      cases n,
      { rw [show i = 0, by { ext, simpa only [nat.lt_one_iff] using i.is_lt, }],
        rw [show q = 0, by linarith],
        unfold P,
        simp only [id_comp, homological_complex.add_f_apply, preadditive.comp_add, homological_complex.id_f],
        erw [comp_id, Hσ, homotopy.null_homotopic_map_f (cs_down_succ 1) (cs_down_succ 0)],
        unfold hσ' hσ,
        simp only [tsub_zero, nat.not_lt_zero, zero_tsub, pow_one, preadditive.comp_add, one_zsmul,
          if_false, eq_to_hom_refl, neg_smul, preadditive.neg_comp, comp_id, pow_zero, preadditive.comp_neg],
        repeat { erw chain_complex.of_d, },
        dsimp,
        simp only [fin.sum_univ_two],
        erw fin.sum_univ_succ,
        simp only [fin.sum_univ_two],
        simp only [fin.coe_zero, fin.coe_one, preadditive.add_comp, pow_one,
          preadditive.comp_add, one_zsmul, neg_smul, preadditive.neg_comp, pow_zero,
          preadditive.comp_neg, neg_sq, one_pow, fin.succ_one_eq_two, fin.coe_two,
          fin.succ_zero_eq_one, neg_add_rev, neg_neg, ← add_assoc],
        have simplif : ∀ (a b c d e f : X _[0] ⟶ X _[1]), a = b → a = c → a = d → a =e → a = f
          → a + b + (-c) + (-d) + e  + (-f) = 0,
        { intros a b c d e f hb hc hd he hf,
          rw [← hb, ← hc, ← hd, ← he, ← hf],
          abel, },
        apply simplif,
        { slice_rhs 1 2 { erw simplicial_object.δ_comp_σ_self, },
          erw id_comp, },
        { slice_rhs 1 2 { erw simplicial_object.δ_comp_σ_succ, },
          erw id_comp, },
        { erw [simplicial_object.δ_comp_σ_succ, comp_id], },
        { erw [simplicial_object.δ_comp_σ_self, comp_id], },
        { erw simplicial_object.δ_comp_σ_of_le X
            (show (0 : fin(2)) ≤ fin.cast_succ 0, by { simp only [fin.cast_succ_zero], }),
          slice_rhs 1 2 { erw simplicial_object.δ_comp_σ_self, },
          erw [id_comp], }, },
      { rw [← id_comp (X.σ i),
          show 𝟙 (X.obj (op [n.succ])) = (P q).f (n+1) + (Q q).f (n+1), by { unfold Q,
            simpa only [homological_complex.sub_f_apply, add_sub_cancel'_right, homological_complex.id_f]}],
        simp only [preadditive.add_comp],
        conv { to_rhs, erw ← zero_add (0 : X.obj (op [n+1]) ⟶ X.obj (op [n+2])), },
        congr,
        { let φ := (P q).f (n+1) ≫ X.σ i,
          have v : higher_faces_vanish q φ := higher_faces_vanish_σφ hi' (higher_faces_vanish_P q n),
          rw [show (P q).f (n+1) ≫ X.σ i = φ, by refl],
          unfold P,
          erw [← assoc, P_is_identity_where_faces_vanish v, homological_complex.add_f_apply,
            preadditive.comp_add, comp_id, Hσφ_eq_neg_σδ hi' v, add_neg_eq_zero],
          dsimp [φ],
          have eq : (⟨(i : ℕ)+1, _⟩ : fin(n+3)) = i.succ, rotate 2,
          { have h := fin.is_lt i,
            simp only [nat.succ_eq_add_one] at h,
            linarith, },
          { ext,
            simp only [fin.coe_succ, fin.coe_mk], },
          slice_rhs 2 3 { erw [eq, simplicial_object.δ_comp_σ_succ X], },
          erw [id_comp],
          refl, },
        { rw [decomposition_Q n q (by { simp only [nat.succ_eq_add_one] at hi', linarith, })],
          simp only [preadditive.sum_comp],
          apply finset.sum_eq_zero,
          intros j hj,
          simp only [true_and, finset.mem_univ, finset.mem_filter] at hj,
          let i' : fin (n+1) := ⟨(i : ℕ), _⟩, swap,
          { by_contradiction h',
            simp only [not_lt] at h',
            simp only [nat.succ_eq_add_one] at hi',
            rw hi' at h',
            simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h',
            rw h' at hj,
            exact nat.not_lt_zero _ hj, },
          rw [show i = fin.cast_succ i', by {ext, simp only [fin.cast_succ_mk, fin.eta], }],
          cases nat.le.dest (nat.lt_succ_iff.mp (fin.is_lt j)) with k hk,
          rw add_comm at hk,
          have eq := simplicial_object.σ_comp_σ X (_ : i' ≤ (reverse_fin j)), swap,
          { simp only [reverse_fin_eq j hk.symm, fin.le_iff_coe_le_coe, fin.coe_mk],
            simp only [nat.succ_eq_add_one] at hi',
            linarith, },
          slice_lhs 3 4 { erw eq, },
          unfold P,
          have eq' := hq (reverse_fin j).succ _, swap,
          { simp only [← hk, reverse_fin_eq j hk.symm, nat.succ_eq_add_one,
              fin.succ_mk, fin.coe_mk],
            linarith, },
          conv { to_lhs, congr, skip, congr, skip, erw ← assoc, congr,
            erw assoc, congr, skip, erw eq', },
          simp only [comp_zero, zero_comp], }, }, }, },
end

lemma P_infty_eq_zero_on_σ (X : simplicial_object C)
  {n : ℕ} (i : fin (n+1)) :
  (X.σ i) ≫ P_infty.f (n+1) = 0 :=
begin
  rw P_infty_degreewise,
  apply P_q_eq_zero_on_σ X i,
  simp only [zero_le, le_add_iff_nonneg_left],
end

lemma P_infty_eq_zero_on_degeneracies (X : simplicial_object C)
  {n : ℕ} {Δ' : simplex_category} (θ : [n] ⟶ Δ')
  (hf : ¬function.injective θ.to_order_hom) :
  X.map θ.op ≫ P_infty.f n = 0 :=
begin
  cases n,
  { exfalso,
    simp only [function.injective, exists_prop, not_forall] at hf,
    rcases hf with ⟨x,y,⟨h₁,h₂⟩⟩,
    have hx := fin.is_lt x,
    have hy := fin.is_lt y,
    simp only [simplex_category.len_mk, nat.lt_one_iff] at hx hy,
    simp only [fin.ext_iff, hx, hy] at h₂,
    exact h₂ rfl, },
  { rcases simplex_category.eq_σ_comp_of_not_injective θ hf with ⟨i,θ,h⟩,
    erw [h, op_comp, X.map_comp, assoc,
      P_infty_eq_zero_on_σ X i, comp_zero], }
end

lemma P_infty_eq_zero_on_Γ_summand (K : chain_complex C ℕ) {n : ℕ} {A : Γ_index_set [n]} (hA : ¬A.1.len = n) :
  inclusion_Γ_summand K A ≫ P_infty.f n = 0 :=
begin
  have h : ¬function.injective A.2.1.to_order_hom,
  { by_contradiction,
    apply hA,
    simpa only [fintype.card_fin, add_left_inj] using
      (fintype.card_of_bijective ⟨h, simplex_category.epi_iff_surjective.mp A.snd.property⟩).symm, },
  haveI : epi A.2.1 := A.2.2,
  rw [show A = ⟨A.1,⟨A.2.1,A.2.2⟩⟩, by { ext1, { simp only [eq_to_hom_refl, comp_id], }, refl, }],
  slice_lhs 1 1 { dsimp, erw ← inclusion_Γ_summand_decomp K A.2.1, },  
  rw [assoc, show Γ_simplicial K A.2.1 = (Γ'.obj K).map A.2.1.op, by refl],
  slice_lhs 2 3 { erw P_infty_eq_zero_on_degeneracies _ A.2.1 h, },
  erw comp_zero,
end

end dold_kan

end algebraic_topology

