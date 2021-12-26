/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebra.homology.homotopy
import algebra.big_operators.basic
import algebraic_topology.simplicial_object
import algebraic_topology.alternating_face_map_complex

import homotopies
open homology

open category_theory
open category_theory.limits
open category_theory.subobject
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.category
open opposite

open_locale big_operators
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

/- construction of homotopies -/

variables {X : simplicial_object C}

def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] := if n<q then 0
  else (-1 : ℤ)^(n-q) • X.σ ⟨n-q, nat.sub_lt_succ n q⟩

@[simp]
lemma hσ_eq_zero {q : ℕ} {n : ℕ} (hnq : n<q) : (hσ q n : X _[n] ⟶ X _[n+1])= 0 :=
begin
  unfold hσ,
  rw ite_eq_left_iff,
  intro h,
  exfalso,
  exact h hnq,
end

@[simp]
lemma hσ_eq {q n a : ℕ} (ha : n=a+q) : (hσ q n : X _[n] ⟶ X _[n+1]) =
    (-1 : ℤ)^a • X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm ha))⟩ :=
begin
  unfold hσ,
  split_ifs,
  { exfalso, linarith, },
  { congr; exact tsub_eq_of_eq_add ha, }
end

@[simp]
def Hσ (q : ℕ) : (alternating_face_map_complex C).obj X ⟶
  (alternating_face_map_complex C).obj X :=
null_homotopic_chain_complex_map (hσ q)

/- definition of the projector P -/

@[simp]
def P : ℕ → ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X)
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ - Hσ q)
/- the sign should be changed?...-/

/- these endormorphismes P q coincide with `𝟙` in degree 0 -/

lemma P_deg0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  induction q with q hq,
  { simp, },
  { simp [hq],
    cases q,
    { erw chain_complex.of_d,
      simp [hσ_eq (show 0=0+0, by refl), alternating_face_map_complex.obj_d],
      rw [fin.sum_univ_two],
      simp only [comp_neg, fin.coe_zero, comp_add, fin.coe_one, pow_one,
        one_zsmul, pow_zero, neg_smul],
      apply add_neg_eq_zero.mpr,
      erw [δ_comp_σ_self, δ_comp_σ_succ], },
    { simp, }, },
end

/- vanishing of some faces -/

structure higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
  (vanishing : ∀ (j : fin (n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0)

@[simp]
def translate_fin {n : ℕ} (a : ℕ) {q : ℕ} (hnaq : n=a+q) (i : fin(q)) : fin(n) :=
⟨a+(i:ℕ), (gt_of_ge_of_gt (eq.ge hnaq) ((add_lt_add_iff_left a).mpr (fin.is_lt i)))⟩

lemma remove_trailing_zero_in_sum {β : Type*} [add_comm_monoid β] {n a q : ℕ} (hnaq : n=a+q)
  (f : fin(n) → β) (hf : ∀ (j : fin(q)), f (translate_fin a hnaq j) = 0) :
  ∑ (i : fin(n)), f i = ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ, f i := 
begin
  let lt_a := λ (i : fin(n)), (i:ℕ)<a,
  have vanishing : ∀ (i : fin(n)), i ∈ (finset.univ : finset(fin(n))) → f i ≠ 0 → lt_a i,
  { intros i hi0,
    by_cases hi1 : lt_a i,
    { intro, assumption, },
    { intro hi2,
      exfalso,
      simp only [not_lt] at hi1,
      cases nat.le.dest hi1 with j hj,
      have hjq : j<q,
      { apply (add_lt_add_iff_left a).mp,
        rw [← hnaq, hj],
        exact fin.is_lt i, },
      have hfj := hf ⟨j, hjq⟩,
      simp only [hj, translate_fin, fin.eta, fin.coe_mk] at hfj,
      exact hi2 hfj, }, },
  simp only [← finset.sum_filter_of_ne vanishing],
end

lemma leave_out_last_term {β : Type*} [add_comm_monoid β] {n a : ℕ} (hna : a<n)
  {f : fin(n) → β} :
  ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a+1) finset.univ, f i = 
  ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ, f i + f ⟨a, hna⟩ :=
begin
  conv { to_rhs, rw add_comm, },
  let S := finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ,
  let b : fin (n) := ⟨a, hna⟩,
  rw ← finset.sum_insert (_ : b ∉ S), swap,
  { simp only [lt_self_iff_false, not_false_iff, finset.mem_filter, fin.coe_mk, and_false], },
  congr',
  ext i,
  simp only [true_and, finset.mem_univ, finset.mem_insert, finset.mem_filter],
  simp only [nat.lt_iff_add_one_le],
  rw [nat.le_add_one_iff],
  conv { to_lhs, congr, skip, rw [add_left_inj 1], },
  conv { to_rhs, rw or.comm, congr, skip, rw [fin.ext_iff, fin.coe_mk], },
end

lemma simplif {β : Type*} [add_comm_group β] {a b c d e f : β} 
  (h1 : e=f) (h2 : b+c=0) (h3 : a+d=0) : a+b+c+(d+e) = f :=
by { rw [add_assoc a b c, h2, add_zero, ← add_assoc a d e, h3, zero_add, h1], }

lemma Hσφ_eq_σδ {Y : C} {n a q : ℕ} (hnaq : n=a+q) (φ : Y ⟶ X _[n+1])
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 
  - φ ≫ X.δ ⟨a+1, nat.succ_lt_succ (nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq)))⟩ ≫
  X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
begin
  have hnaq_shift : Π d : ℕ, n+d=(a+d)+q,
  { intro d, rw [add_assoc, add_comm d, ← add_assoc, hnaq], },
  simp only [Hσ, hσ_eq hnaq, hσ_eq (hnaq_shift 1), null_homotopic_chain_complex_map_f_2,
    null_homotopic_chain_complex_map_f, comp_add],
  repeat { erw chain_complex.of_d, },
  simp only [alternating_face_map_complex.obj_d, comp_sum, sum_comp],
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul],
  have ineq1 : a<n+1 := nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq)),
  have ineq2 : a+1< n+2 := nat.succ_lt_succ ineq1,
  let term1 := λ (j : fin (n+3)), ((-1 : ℤ)^(a+1) * (-1 : ℤ)^(j : ℕ)) • (φ ≫ X.σ ⟨a+1, ineq2⟩) ≫ X.δ j,
  let term2 := λ (j : fin (n+2)), ((-1 : ℤ)^(j : ℕ) * (-1 : ℤ)^a) • (φ ≫ X.δ j) ≫ X.σ ⟨a, ineq1⟩,
  let j : fin(n+1) := ⟨n-q, nat.sub_lt_succ n q⟩,
  simp only [← term1, ← term2],
  /- cleaning up the first sum -/
  rw remove_trailing_zero_in_sum (hnaq_shift 3) term1, swap,
  { intro k,
    simp only [term1],
    have hk := fin.is_lt k,
    let i : fin(n+1) := ⟨a+1+(k : ℕ), by linarith⟩,
    have hia : fin.cast_succ (⟨a+1, by linarith⟩ : fin(n+1)) < i.succ,
    { simp only [fin.lt_iff_coe_lt_coe, fin.succ_mk, fin.cast_succ_mk,
        add_lt_add_iff_right, fin.coe_mk],
      linarith, },
    have δσ_rel := δ_comp_σ_of_gt X hia,
    have hisucc : i.succ.succ = translate_fin (a+3) (hnaq_shift 3) k,
    { ext, simp only [fin.succ_mk, translate_fin, fin.coe_mk], linarith, },
    rw [hisucc, fin.cast_succ_mk] at δσ_rel,
    rw [assoc, δσ_rel],
    have eq := v.vanishing i (by { simp only [i, fin.coe_mk], linarith, }),
    rw [← assoc, eq],
    simp only [smul_zero', zero_comp], },
  /- cleaning up the second sum -/
  rw remove_trailing_zero_in_sum (hnaq_shift 2) term2, swap,
  { intro k,
    simp only [term2],
    have hk := fin.is_lt k,
    let i : fin (n+1) := ⟨a+k+1, by linarith⟩,
    have eq := v.vanishing i (by { simp only [i, fin.coe_mk], linarith, }),
    have hi : translate_fin (a+2) (hnaq_shift 2) k = i.succ,
    { ext, simp only [fin.succ_mk, translate_fin, fin.coe_mk], linarith, },
    rw [hi, eq],
    simp only [smul_zero', zero_comp], },
  /- -/
  rw [leave_out_last_term (ineq2 : a+1<n+2),
    leave_out_last_term (show a+2<n+3, by linarith),
    leave_out_last_term (show a+1<n+3, by linarith)],
  apply simplif,
  { simp only [term2],
    rw fin.coe_mk,
    have eq : (-1 : ℤ)^(a+1) * (-1 : ℤ)^a = -1,
    { calc (-1 : ℤ)^(a+1)*(-1 : ℤ)^a  = - ((-1 : ℤ)^a*(-1 : ℤ)^a) : by ring_exp
      ...                             = - ((-1 : ℤ)*(-1 : ℤ))^a : by rw ← mul_pow
      ...                             = - 1^a : by ring
      ...                             = - 1   : by ring_exp },
    rw [eq, neg_smul, one_zsmul, assoc], },
  { simp only [term1],
    let b : fin(n+2) := ⟨a+1, ineq2⟩,
    have eq1 : X.σ b ≫ X.δ (fin.cast_succ b) = 𝟙 _ := by rw δ_comp_σ_self,
    have eq2 : X.σ b ≫ X.δ b.succ = 𝟙 _ := by rw δ_comp_σ_succ,
    simp only [b, fin.cast_succ_mk, fin.succ_mk] at eq1 eq2,
    rw [assoc, assoc, eq1, eq2],
    simp only [comp_id, fin.coe_mk],
    apply add_eq_zero_iff_eq_neg.mpr,
    have eq3 : (-1 : ℤ)^(a+2) = (-1 : ℤ) * (-1 : ℤ)^(a+1),
    { have eq4 := pow_add (-1 : ℤ) 1 (a+1),
      rw pow_one at eq4,
      congr' 1, },
    simp only [eq3, neg_mul_eq_neg_mul_symm, one_mul,
      mul_neg_eq_neg_mul_symm, neg_neg, neg_smul], },
  { let ι : fin (n+2) → fin (n+3) := fin.cast_succ,
    let S := finset.filter (λ i : fin(n+2), (i:ℕ)<a+1) finset.univ,
    let T := finset.filter (λ i : fin(n+3), (i:ℕ)<a+1) finset.univ,
    have eq : ∑ (s : fin(n+2)) in S, term1 (ι s) =
              ∑ (t : fin(n+3)) in T, term1 t    := finset.sum_bij (λ (s : fin(n+2))
      (hs : s ∈ finset.filter (λ i : fin(n+2), (i:ℕ)<a+1) finset.univ), ι s) _ _ _ _, rotate,
      { intros a ha,
        simp only [true_and, finset.mem_univ, fin.coe_cast_succ,
          finset.mem_filter] at ha ⊢,
        assumption, },
      { intros a ha, refl, },
      { intros a b ha hb H,
        simp only [order_embedding.eq_iff_eq] at H,
        rw H, },
      { intros b hb,
        simp only [true_and, finset.mem_univ, fin.coe_cast_succ,
          finset.mem_filter] at hb,
        have hb2 : (b:ℕ) < n+2 := by linarith,
        use (⟨(b : ℕ), hb2⟩ : fin(n+2)),
        split,
          { simp only [true_and, finset.mem_univ, finset.mem_filter, fin.coe_mk], exact hb, },
          { simp only [ι, fin.cast_succ_mk, fin.eta], }, },
    { rw [← eq, ← finset.sum_add_distrib],
      apply finset.sum_eq_zero,
      intros i hi,
      simp only [term1, term2],
      repeat { rw assoc, },
      simp only [true_and, finset.mem_univ, finset.mem_filter] at hi,
    have hia : i≤ fin.cast_succ (⟨a, by linarith⟩ : fin(n+1)),
    { simp only [fin.cast_succ_mk],
      rw fin.le_iff_coe_le_coe,
      simp only [fin.coe_mk],
      linarith, },
    have δσ_rel := δ_comp_σ_of_le X hia,
    simp only [fin.succ_mk] at δσ_rel,
    rw δσ_rel,
    apply add_eq_zero_iff_eq_neg.mpr,
    rw ← neg_smul,
    congr',
    simp only [fin.coe_cast_succ],
    ring_exp, }
  },
end

#exit

lemma Hσφ_eq_zero {Y : C} {n : ℕ} (q : ℕ) (hqn : n<q) (φ : Y ⟶ X _[n+1])
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  by_cases hqnp : n+1<q,
  { simp [Hσ],
    rw [hσ_eq_zero hqn, hσ_eq_zero hqnp],
    simp only [add_zero, zero_comp, comp_zero], },
  { have eqq := le_antisymm (not_lt.mp hqnp) (nat.succ_le_iff.mpr hqn),
    simp,
    rw hσ_eq (show n+1=0+q, by linarith),
    simp only [fin.mk_zero, fin.mk_eq_subtype_mk, one_zsmul, pow_zero],
    erw chain_complex.of_d,
    simp only [alternating_face_map_complex.obj_d,
      hσ_eq_zero hqn, add_zero, comp_zero, comp_sum],
    have h2 : n+3=2+(n+1) := by linarith,
    rw [remove_trailing_zero_in_sum' h2],
    { rw fin.sum_univ_two,
      simp only [comp_neg, fin.coe_zero, fin.coe_one, pow_one, fin.coe_cast_le,
        one_zsmul, neg_smul, pow_zero, fin.cast_le_zero],
      apply add_neg_eq_zero.mpr,
      erw [δ_comp_σ_self, δ_comp_σ_succ], },
    { intros j,
      simp only [comp_zsmul],
      have δσ_rel := δ_comp_σ_of_gt X (_ : fin.cast_succ (0 : fin(n+1))<j.succ),
      swap, rw fin.cast_succ_zero, exact fin.succ_pos j,
      have translate_2 : j.succ.succ = translate_fin 2 h2 j,
      { ext,
        simp only [fin.coe_succ, translate_fin, fin.mk_eq_subtype_mk, fin.coe_mk],
        linarith, },
      rw translate_2 at δσ_rel,
      erw δσ_rel,
      have dφ := v.vanishing j _, swap, rw eqq, exact le_add_self,
      rw [← assoc, dφ],
      simp only [smul_zero', zero_comp], }, },
end

lemma higher_faces_vanish_ind {Y : C} {n : ℕ} (q : ℕ) {φ : Y ⟶ X _[n+1]} 
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ - Hσ q).f (n+1)) :=
{ vanishing :=
  begin
      sorry
  end
}

end dold_kan

end algebraic_topology

