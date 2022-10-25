/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.decomposition
import tactic.fin_cases
import algebraic_topology.split_simplicial_object

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
statement `σ_comp_P_eq_zero` which is obtained for the `P q`
by induction on `q : ℕ`.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.idempotents
  category_theory.preadditive opposite
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

lemma higher_faces_vanish.comp_σ {Y : C} {X : simplicial_object C} {n b q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) (hnbq : n + 1 = b + q) :
    higher_faces_vanish q (φ ≫ X.σ ⟨b,
    by simpa only [hnbq, nat.lt_succ_iff, le_add_iff_nonneg_right] using zero_le q⟩) := λ j hj₁,
begin
  rw assoc,
  have eq := simplicial_object.δ_comp_σ_of_gt X (_ : fin.cast_succ ⟨b, _⟩ < j), rotate,
  { rw [hnbq, lt_add_iff_pos_right],
    by_contradiction,
    simp only [not_lt, nonpos_iff_eq_zero] at h,
    rw [h, add_zero] at hj₁,
    have pif := lt_of_le_of_lt hj₁ (fin.is_lt j),
    simpa only [lt_self_iff_false] using lt_of_le_of_lt hj₁ (fin.is_lt j), },
  { rw [fin.cast_succ_mk, fin.lt_iff_coe_lt_coe, fin.coe_mk, nat.lt_iff_add_one_le,
      ← add_le_add_iff_right q, add_assoc, add_comm 1, ← add_assoc, ← hnbq],
    exact hj₁, },
  simp only [fin.cast_succ_mk] at eq,
  have hj₂ : j ≠ 0,
  { intro hj₃,
    simpa only [hj₃, hnbq, fin.coe_zero, zero_add, add_comm b, add_assoc, add_le_iff_nonpos_right,
      le_zero_iff, add_eq_zero_iff, nat.one_ne_zero, false_and] using hj₁, },
  rw [eq, ← assoc],
  conv_lhs { congr, congr, skip, rw ← fin.succ_pred j hj₂, },
  rw [v (j.pred hj₂), zero_comp],
  rw [← add_le_add_iff_right 1, add_assoc _ q, add_comm q 1, ← add_assoc,
      ← fin.coe_succ, fin.succ_pred],
  exact hj₁,
end

lemma σ_comp_P_eq_zero (X : simplicial_object C)
  {n q : ℕ} : ∀ (i : fin (n + 1)) (hi : n + 1 ≤ i + q),
  (X.σ i) ≫ (P q).f (n + 1) = 0 :=
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
        rw [← nat.lt_succ_iff, nat.succ_eq_add_one, add_assoc, hj, not_lt,
          add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h,
        rw [← add_left_inj 1, add_assoc, hj, self_eq_add_right, h], },
      cases n,
      { fin_cases i,
        rw [show q = 0, by linarith],
        unfold P,
        simp only [id_comp, homological_complex.add_f_apply, comp_add, homological_complex.id_f],
        erw [comp_id, Hσ, homotopy.null_homotopic_map'_f (c_mk 2 1 rfl) (c_mk 1 0 rfl)],
        unfold hσ' hσ,
        simp only [nat.not_lt_zero, if_false, tsub_zero, pow_zero, pow_one, one_zsmul,
          neg_smul, comp_add, neg_comp, comp_neg, eq_to_hom_refl,comp_id,
          alternating_face_map_complex.obj_d_eq],
        dsimp,
        erw [fin.sum_univ_two, fin.sum_univ_succ, fin.sum_univ_two],
        simp only [fin.coe_zero, pow_zero, one_zsmul, fin.coe_one, pow_one, neg_smul,
          add_comp, neg_comp, comp_add, comp_neg, neg_add_rev, neg_neg, ← add_assoc,
          fin.succ_zero_eq_one, fin.succ_one_eq_two, fin.coe_two, neg_one_sq],
        have simplif : ∀ (a b c d e f : X _[0] ⟶ X _[1]), a = b → a = c → a = d → a = e →
          a = f → a + b + (-c) + (-d) + e  + (-f) = 0,
        { intros a b c d e f hb hc hd he hf,
          rw [← hb, ← hc, ← hd, ← he, ← hf],
          abel, },
        apply simplif,
        { erw simplicial_object.δ_comp_σ_self_assoc, },
        { erw simplicial_object.δ_comp_σ_succ_assoc, },
        { erw [simplicial_object.δ_comp_σ_succ, comp_id], },
        { erw [simplicial_object.δ_comp_σ_self, comp_id], },
        { erw simplicial_object.δ_comp_σ_of_le X
            (show (0 : fin(2)) ≤ fin.cast_succ 0, by rw fin.cast_succ_zero),
          erw simplicial_object.δ_comp_σ_self_assoc, }, },
      { rw [← id_comp (X.σ i), ← (P_add_Q_f q n.succ : _ = 𝟙 (X.obj _)), add_comp, add_comp,
          ← zero_add (0 : X.obj (op [n+1]) ⟶ X.obj (op [n+2]))],
        congr,
        { have v : higher_faces_vanish q ((P q).f n.succ ≫ X.σ i) :=
            (higher_faces_vanish.of_P q n).comp_σ hi',
          unfold P,
          erw [← assoc, v.comp_P_eq_self, homological_complex.add_f_apply,
            preadditive.comp_add, comp_id, v.comp_Hσ_eq hi', add_neg_eq_zero, assoc],
          rw simplicial_object.δ_comp_σ_succ'_assoc, swap,
          { ext,
            simp only [fin.coe_mk, fin.coe_succ], },
          refl, },
        { simp only [decomposition_Q n q, preadditive.sum_comp],
          apply finset.sum_eq_zero,
          intros j hj,
          simp only [true_and, finset.mem_univ, finset.mem_filter] at hj,
          let i' : fin (n + 1) := ⟨(i : ℕ), _⟩, swap,
          { by_contradiction h',
            simp only [not_lt] at h',
            simp only [nat.succ_eq_add_one] at hi',
            rw hi' at h',
            simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at h',
            rw h' at hj,
            exact nat.not_lt_zero _ hj, },
          obtain ⟨k, hk⟩ := nat.le.dest (nat.lt_succ_iff.mp (fin.is_lt j)),
          rw add_comm at hk,
          rw [show i = fin.cast_succ i', by { ext, simp only [fin.cast_succ_mk, fin.eta], },
            assoc, assoc, assoc, simplicial_object.σ_comp_σ_assoc], swap,
          { simp only [reverse_fin_eq j hk.symm, fin.le_iff_coe_le_coe, fin.coe_mk],
            simp only [nat.succ_eq_add_one] at hi',
            linarith, },
          unfold P,
          have eq' := hq (reverse_fin j).succ _, swap,
          { simp only [← hk, reverse_fin_eq j hk.symm, nat.succ_eq_add_one,
              fin.succ_mk, fin.coe_mk],
            linarith, },
          simp only [assoc, homological_complex.comp_f, reassoc_of eq', zero_comp, comp_zero], }, }, }, },
end

lemma σ_comp_P_infty (X : simplicial_object C)
  {n : ℕ} (i : fin (n+1)) :
  (X.σ i) ≫ P_infty.f (n+1) = 0 :=
begin
  rw P_infty_f,
  apply σ_comp_P_eq_zero X i,
  simp only [zero_le, le_add_iff_nonneg_left],
end

@[reassoc]
lemma P_infty_on_degeneracies (X : simplicial_object C)
  (n : ℕ) {Δ' : simplex_category} (θ : [n] ⟶ Δ')
  (hθ : ¬mono θ) :
  X.map θ.op ≫ P_infty.f n = 0 :=
begin
  rw simplex_category.mono_iff_injective at hθ,
  cases n,
  { exfalso,
    apply hθ,
    intros x y h,
    fin_cases x,
    fin_cases y, },
  { rcases simplex_category.eq_σ_comp_of_not_injective θ hθ with ⟨i, α, h⟩,
    rw [h, op_comp, X.map_comp, assoc, (show X.map (simplex_category.σ i).op = X.σ i, by refl),
      σ_comp_P_infty, comp_zero], },
end

end dold_kan

end algebraic_topology
