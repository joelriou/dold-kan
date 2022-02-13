/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.homotopies
import algebra.big_operators.fin
import data.nat.parity

open nat
open category_theory
open category_theory.limits
open category_theory.category
open category_theory.preadditive
open category_theory.simplicial_object
open_locale simplicial
open_locale big_operators


namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

structure higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
(vanishing : ∀ (j : fin (n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0)

/-- the map `λ a, a+i` from `fin` q to `fin n`, when $n=a+q$ -/
@[simp]
def translate_fin {n : ℕ} (a : ℕ) {q : ℕ} (hnaq : n=a+q) (i : fin q) : fin n :=
⟨a+(i:ℕ), (gt_of_ge_of_gt (eq.ge hnaq) ((add_lt_add_iff_left a).mpr (fin.is_lt i)))⟩

@[to_additive]
lemma prod_split {β : Type*} [comm_monoid β] {n a b : ℕ}
  (h : n=a+b) (f : fin(n) → β) :
  ∏ (i : fin (n)), f i =
  (∏ (i : fin (a)), f (fin.cast_le (nat.le.intro (eq.symm h)) i)) *
  ∏ (i : fin (b)), f (translate_fin a h i) :=
begin
  revert f a n,
  induction b with b hb,
  { intros n a hnaq f,
    rw add_zero at hnaq,
    subst hnaq,
    simp only [fin.prod_univ_zero, mul_one],
    congr,
    ext i,
    congr,
    ext,
    rw fin.coe_cast_le, },
  { intros n a h f,
    have h' : n = (a+1)+b := by { rw [h, succ_eq_add_one], linarith, },
    rw [hb h' f, fin.prod_univ_cast_succ, mul_assoc],
    conv { to_rhs, rw fin.prod_univ_succ, },
    congr,
    ext,
    congr' 1,
    ext,
    simp only [translate_fin, fin.coe_mk, fin.coe_succ],
    rw [add_assoc, add_comm 1], }
end

@[to_additive]
lemma prod_trunc {β : Type*} [comm_monoid β] {n a b : ℕ}
  (h : n=a+b) (f : fin(n) → β)
  (hf : ∀ (j : fin (b)), f (translate_fin a h j) = 1) :
  ∏ (i : fin (n)), f i =
  ∏ (i : fin (a)), f (fin.cast_le (nat.le.intro (eq.symm h)) i) :=
begin
  rw prod_split h,
  conv { to_lhs, congr, skip, rw fintype.prod_eq_one _ hf, },
  rw mul_one,
end

lemma Hσφ_eq_neg_σδ {Y : C} {n a q : ℕ} (hnaq : n=a+q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) =
  - φ ≫ X.δ ⟨a+1, nat.succ_lt_succ (nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq)))⟩ ≫
  X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
begin
  have hnaq_shift : Π d : ℕ, n+d=(a+d)+q,
  { intro d, rw [add_assoc, add_comm d, ← add_assoc, hnaq], },
  rw [Hσ, homotopy.null_homotopic_map_f (cs_down_succ (n+1)) (cs_down_succ n),
    hσ'_eq hnaq (cs_down_succ n), hσ'_eq (hnaq_shift 1) (cs_down_succ (n+1))],
  repeat { erw chain_complex.of_d, },
  simp only [alternating_face_map_complex.obj_d, eq_to_hom_refl, comp_id,
    comp_sum, sum_comp, comp_id, comp_add],
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul],
  /- cleaning up the first sum -/
  rw sum_trunc (hnaq_shift 2), swap,
  { rintro ⟨k, hk⟩,
    let i : fin (n+1) := ⟨a+k+1, by linarith⟩,
    have eq := v.vanishing i (by { simp only [i, fin.coe_mk], linarith, }),
    have hi : translate_fin (a+2) (hnaq_shift 2) ⟨k, hk⟩ = i.succ,
    { ext, simp only [translate_fin, fin.coe_mk, fin.succ_mk], linarith, },
    rw [hi, eq, zero_comp, zsmul_zero], },
  /- cleaning up the second sum -/
  rw sum_trunc (hnaq_shift 3), swap,
  { rintros ⟨k, hk⟩,
    simp only [translate_fin, fin.coe_mk, assoc],
    let i : fin (n+1) := ⟨a+1+(k : ℕ), by linarith⟩,
    have h : fin.cast_succ (⟨a+1, by linarith⟩ : fin(n+1)) < i.succ,
    { simp only [fin.lt_iff_coe_lt_coe, fin.cast_succ_mk, fin.coe_mk, fin.succ_mk],
      linarith, },
    have δσ_rel := δ_comp_σ_of_gt X h,
    simp only [fin.cast_succ_mk] at δσ_rel,
    conv at δσ_rel { to_lhs,
      simp only [fin.succ_mk, fin.succ_mk, show a+1+k+1+1 = a+3+k, by linarith], },
    simp only [δσ_rel, ← assoc, zero_comp, zsmul_zero,
      v.vanishing i (by { simp only [i, fin.coe_mk], linarith, })], },
  /- leaving out three specific terms -/
  conv { to_lhs, congr, skip, rw [fin.sum_univ_cast_succ, fin.sum_univ_cast_succ ], },
  rw fin.sum_univ_cast_succ,
  /- the purpose of the following `simplif` is to create three subgoals in order
    to finish the proof -/
  have simplif : ∀ (a b c d e f : Y ⟶ X _[n+1]), b=f → d+e=0 → c+a=0 → a+b+(c+d+e) =f,
  { intros a b c d e f h1 h2 h3,
    rw [add_assoc c d e, h2, add_zero, add_comm a b, add_assoc,
      add_comm a c, h3, add_zero, h1], },
  apply simplif,
  { /- b=f -/
    have eq : (-1 : ℤ)^(a+1) * (-1 : ℤ)^a = -1 := begin
      rw ← pow_add,
      apply neg_one_pow_of_odd,
      use a,
      linarith,
    end,
    simp only [eq, fin.last, fin.cast_le_mk, fin.coe_mk, neg_smul, one_zsmul], },
  { /- d+e = 0 -/
    let b : fin(n+2) := ⟨a+1, nat.succ_lt_succ $ nat.lt_succ_iff.mpr $
      nat.le.intro (eq.symm hnaq)⟩,
    have eq1 : X.σ b ≫ X.δ (fin.cast_succ b) = 𝟙 _ := by rw δ_comp_σ_self,
    have eq2 : X.σ b ≫ X.δ b.succ = 𝟙 _ := by rw δ_comp_σ_succ,
    simp only [b, fin.cast_succ_mk, fin.succ_mk] at eq1 eq2,
    simp only [eq1, eq2, fin.last, assoc, fin.cast_succ_mk, fin.cast_le_mk, fin.coe_mk,
      comp_id, add_eq_zero_iff_eq_neg, ← neg_zsmul],
    congr,
    ring_exp,
    rw mul_one, },
  { /- c+a = 0 -/
    rw ← finset.sum_add_distrib,
    apply finset.sum_eq_zero,
    rintros ⟨i, hi⟩ h₀,
    have hia : (⟨i, by linarith⟩ : fin(n+2)) ≤ fin.cast_succ (⟨a, by linarith⟩ : fin(n+1)) :=
      by simpa only [fin.le_iff_coe_le_coe, fin.coe_mk, fin.cast_succ_mk, ← lt_succ_iff] using hi,
    simp only [fin.coe_mk, fin.cast_le_mk, fin.cast_succ_mk, fin.succ_mk, assoc,
      ← δ_comp_σ_of_le X hia, add_eq_zero_iff_eq_neg, ← neg_zsmul],
    congr,
    ring_exp, },
end

lemma Hσφ_eq_zero {Y : C} {n q : ℕ} (hqn : n<q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  sorry
end

lemma higher_faces_vanish_ind {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ + Hσ q).f (n+1)) :=
begin
  sorry
end

lemma downgrade_vanishing {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish (q+1) φ) : higher_faces_vanish q φ :=
{ vanishing := λ j hj, v.vanishing j (by { rw ← add_assoc, exact le_add_right hj, }) }

end dold_kan

end algebraic_topology
