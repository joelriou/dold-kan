/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.decomposition
import for_mathlib.dold_kan.functor_gamma
import tactic.fin_cases

/-!

# Behaviour of P_infty with respect to degeneracies

For any `X : simplicial_object C` where `C` is an abelian category,
the projector `P_infty : K[X] ⟶ K[X]` is supposed to be the projection
on the normalized subcomplex, parallel to the degenerate subcomplex, i.e.
the subcomplex generated by the images of all `X.σ i`.

In this file, we obtain `P_infty_on_degeneracies` which states that
if `X : simplicial_object C` with `C` a preadditive,
`θ : [n] ⟶ Δ'` is a non injective map in `simplex_category`, then
`X.map θ.op ≫ P_infty.f n = 0`. It follows from the more precise
statement `σ_comp_P_q_eq_zero` which is obtained for the `P q`
by induction on `q : ℕ`.

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

lemma higher_faces_vanish_σφ {Y : C} {X : simplicial_object C} {n b q : ℕ} (hnbq : n+1=b+q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : higher_faces_vanish q (φ ≫ X.σ ⟨b,
    by { rw [hnbq, nat.lt_succ_iff, le_add_iff_nonneg_right], exact zero_le q, }⟩) := λ j hj,
begin
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
  have eq' := v (j.pred _) _, rotate,
  { intro hj',
    rw [hj', hnbq] at hj,
    simpa only [fin.coe_zero, zero_add, add_comm b, add_assoc,
      nat.one_ne_zero, add_le_iff_nonpos_right, add_eq_zero_iff, nonpos_iff_eq_zero, false_and] using hj, },
  { rw [← add_le_add_iff_right 1, add_assoc _ q, add_comm q 1, ← add_assoc,
      ← fin.coe_succ, fin.succ_pred],
    exact hj, },
  simp only [fin.succ_pred] at eq',
  rw [eq', zero_comp],
end

lemma σ_comp_P_q_eq_zero (X : simplicial_object C)
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
        erw [comp_id, Hσ, homotopy.null_homotopic_map_f (c_mk 2 1 rfl) (c_mk 1 0 rfl)],
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
          fin.succ_zero_eq_one, neg_add_rev, neg_neg, ← add_assoc,
          eq_self_iff_true, if_true],
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
          have v : higher_faces_vanish q φ := higher_faces_vanish_σφ hi' (higher_faces_vanish.of_P q n),
          rw [show (P q).f (n+1) ≫ X.σ i = φ, by refl],
          unfold P,
          erw [← assoc, v.comp_P_eq_self, homological_complex.add_f_apply,
            preadditive.comp_add, comp_id, v.comp_Hσ_eq hi', add_neg_eq_zero],
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
        { simp only [decomposition_Q n q, preadditive.sum_comp],
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

lemma σ_comp_P_infty (X : simplicial_object C)
  {n : ℕ} (i : fin (n+1)) :
  (X.σ i) ≫ P_infty.f (n+1) = 0 :=
begin
  rw P_infty_f,
  apply σ_comp_P_q_eq_zero X i,
  simp only [zero_le, le_add_iff_nonneg_left],
end

lemma P_infty_on_degeneracies (X : simplicial_object C)
  {n : ℕ} {Δ' : simplex_category} (θ : [n] ⟶ Δ')
  (hf : ¬function.injective θ.to_order_hom) :
  X.map θ.op ≫ P_infty.f n = 0 :=
begin
  cases n,
  { exfalso,
    apply hf,
    intros x y h,
    fin_cases x,
    fin_cases y, },
  { rcases simplex_category.eq_σ_comp_of_not_injective θ hf with ⟨i, θ, h⟩,
    rw [h, op_comp, X.map_comp, assoc, (show X.map (simplex_category.σ i).op = X.σ i, by refl),
      σ_comp_P_infty, comp_zero], }
end

end dold_kan

end algebraic_topology
