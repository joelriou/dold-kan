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

def Hσ (q : ℕ) : (alternating_face_map_complex C).obj X ⟶
  (alternating_face_map_complex C).obj X :=
null_homotopic_chain_complex_map (hσ q)

/- definition of the projector P -/

@[simp]
def P : ℕ → ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X)
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ + Hσ q)

/- these endormorphismes P q coincide with `𝟙` in degree 0 -/

lemma P_deg0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  induction q with q hq,
  { simp, },
  { simp [Hσ, hq],
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

/- computation of the null_homotopic mapt Hσ -/

structure higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
  (vanishing : ∀ (j : fin (n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0)

@[simp]
def translate_fin {n : ℕ} (a : ℕ) {q : ℕ} (hnaq : n=a+q) (i : fin(q)) : fin(n) :=
⟨a+(i:ℕ), (gt_of_ge_of_gt (eq.ge hnaq) ((add_lt_add_iff_left a).mpr (fin.is_lt i)))⟩

lemma remove_trailing_zeros_in_sum {β : Type*} [add_comm_monoid β] {n a q : ℕ} (hnaq : n=a+q)
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

lemma Hσφ_eq_neq_σδ {Y : C} {n a q : ℕ} (hnaq : n=a+q) {φ : Y ⟶ X _[n+1]}
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
  rw remove_trailing_zeros_in_sum (hnaq_shift 3) term1, swap,
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
  rw remove_trailing_zeros_in_sum (hnaq_shift 2) term2, swap,
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
  have simplif : ∀ (a b c d e f : Y ⟶ X _[n+1]), e=f → b+c=0 → a+d=0 → a+b+c+(d+e) =f,
  { intros a b c d e f h1 h2 h3,
    rw [add_assoc a b c, h2, add_zero, ← add_assoc a d e, h3, zero_add, h1], },
  apply simplif _ _ _ _ _ _,
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

lemma Hσφ_eq_zero {Y : C} {n q : ℕ} (hqn : n<q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  by_cases hqnp : n+1<q;
  simp only [Hσ, null_homotopic_chain_complex_map_f_2,
      null_homotopic_chain_complex_map_f, hσ_eq_zero hqn],
  { simp only [hσ_eq_zero hqnp, add_zero, zero_comp, comp_zero], },
  { have eqq := le_antisymm (not_lt.mp hqnp) (nat.succ_le_iff.mpr hqn),
    simp only [hσ_eq (show n+1=0+q, by linarith), pow_zero, one_zsmul],
    erw chain_complex.of_d,
    simp only [alternating_face_map_complex.obj_d, add_zero, comp_zero, comp_sum],
    rw remove_trailing_zeros_in_sum (show n+3=2+(n+1), by linarith),
    { rw [leave_out_last_term (show 1<n+3, by linarith),
        leave_out_last_term (show 0<n+3, by linarith)],
      rw [finset.sum_eq_zero], swap,
      { intros x hx,
        exfalso,
        simpa only [finset.not_mem_empty, nat.not_lt_zero, finset.filter_false] using hx, },
      simp only [fin.mk_zero, comp_neg, fin.coe_zero, comp_add, fin.coe_one,
        pow_one, one_zsmul, zero_add, neg_smul, fin.mk_one, pow_zero],
      apply add_neg_eq_zero.mpr,
      erw [δ_comp_σ_self, δ_comp_σ_succ], },
    { intro j,
      simp only [comp_zsmul, fin.mk_zero],
      have δσ_rel := δ_comp_σ_of_gt X (_ : fin.cast_succ (0 : fin(n+1))<j.succ),
      swap, rw fin.cast_succ_zero, exact fin.succ_pos j,
      simp only [fin.cast_succ_zero] at δσ_rel,
      have h1 : j.succ.succ = translate_fin 2 _ j,
      { simp only [translate_fin],
        ext,
        simp only [fin.coe_succ, fin.coe_mk],
        linarith, },
      swap, { rw [show 2+(n+1)=((n+1)+1)+1, by linarith], },
      rw h1 at δσ_rel,
      rw δσ_rel,
      have dφ := v.vanishing j _, swap, rw eqq, exact le_add_self,
      simp only [← assoc, dφ, zero_comp, smul_zero'], }, },
end

lemma higher_faces_vanish_ind {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]} 
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ + Hσ q).f (n+1)) :=
{ vanishing :=
  begin
    intros j hj,
    simp only [add_comp, comp_add, homological_complex.add_f_apply, homological_complex.id_f],
    erw comp_id,
    -- when n < q, the result follows immediately from the assumtion
    by_cases hqn : n<q,
    { rw [Hσφ_eq_zero hqn v, zero_comp, add_zero, v.vanishing j (by linarith)], },
    -- we now assume that n≥q, and write n=a+q
    rw [not_lt] at hqn,
    cases nat.le.dest hqn with a ha,
    rw [Hσφ_eq_neq_σδ (show n=a+q, by linarith) v,
      neg_comp, add_neg_eq_zero, assoc, assoc],
    cases n with m hm,
    -- the boundary case n=0
    { simp only [nat.eq_zero_of_add_eq_zero_left ha, fin.eq_zero j,
        fin.mk_zero, fin.mk_one],
      erw [δ_comp_σ_succ],
      simp only [fin.succ_zero_eq_one, comp_id], },
    -- in the other cases, we need to write n as m+1
    { by_cases hj1 : m.succ+1≤(j : ℕ)+q,
      { have hj0 := fin.is_lt j,
        have ham : a≤m,
        { by_contradiction,
          rw [not_le, ← nat.succ_le_iff] at h,
          linarith, },
        have haj : a<(j:ℕ) := by linarith,
        have ineq1 : (fin.cast_succ (⟨a, nat.lt_succ_iff.mpr ham⟩ : fin(m+1)) < j),
        { rw fin.lt_iff_coe_lt_coe, exact haj, },
        erw [δ_comp_σ_of_gt X ineq1],
        -- we shall deal with the case a=m, i.e q=0 separately later
        by_cases ha' : a<m,
        { have ineq2 : (fin.cast_succ (⟨a+1, nat.succ_lt_succ ha'⟩ : fin(m+1)) ≤ j),
          { simp only [fin.le_iff_coe_le_coe, fin.cast_succ_mk, fin.eta, fin.coe_mk],
            exact nat.succ_le_iff.mpr haj, },
          have δδ_rel := δ_comp_δ X ineq2,
          simp only [fin.cast_succ_mk, fin.eta] at δδ_rel,
          slice_rhs 2 3 { erw [← δδ_rel], },
          simp only [← assoc],
          repeat { rw v.vanishing j (by linarith), },
          simp only [zero_comp], },
        { -- case where a=m, q=0, j=m+1
          have eqa1 : a=m := le_antisymm ham (not_lt.mp ha'),
          have eqq  : q=1,
          { simp [← eqa1] at ha,
            rw [show a.succ=a+1, by refl] at ha,
            rw add_comm at ha,
            exact (add_right_inj a).mp ha, },
          have eqa2 : a+1 = (j : ℕ) := by linarith,
          have eqj : (⟨a+1, by linarith⟩ : fin (m+3)) = (fin.cast_succ j),
          { ext, simpa [fin.coe_cast_succ, fin.coe_mk] using eqa2, },
          rw eqj,
          slice_rhs 2 3 { rw δ_comp_δ_self, },
          repeat { rw [← assoc], },
          repeat { rw v.vanishing j (by linarith), },
          simp only [zero_comp], }, },
      { simp [show a = (j : ℕ), by linarith],
        erw [δ_comp_σ_succ],
        simp only [comp_id],
        congr,
        ext,
        simp only [fin.coe_succ, fin.coe_mk], }, },
  end }

lemma higher_faces_vanish_P : Π (q : ℕ),
  Π (n : ℕ), higher_faces_vanish q (((P q).f (n+1) : X _[n+1] ⟶ X _[n+1]))
| 0    := λ n, { vanishing := by
            { intros j hj, exfalso, have hj2 := fin.is_lt j, linarith, } }
|(q+1) := λ n, { vanishing := 
            (higher_faces_vanish_ind (higher_faces_vanish_P q n)).vanishing }

lemma downgrade_vanishing {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish (q+1) φ) : higher_faces_vanish q φ :=
{ vanishing :=
  begin
    intros j hj,
    apply v.vanishing j,
    rw ← add_assoc,
    exact le_add_right hj,
  end }

lemma P_is_identity_where_faces_vanish {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]} 
  (v : higher_faces_vanish q φ) : φ ≫ (P q).f (n+1) = φ :=
begin
  induction q with q hq,
  { unfold P,
    simp only [homological_complex.id_f, comp_id],
    erw [comp_id], },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id, ← assoc],
    simp only [hq (downgrade_vanishing v)],
    apply add_right_eq_self.mpr,
    by_cases hqn : n<q,
    { exact Hσφ_eq_zero hqn (downgrade_vanishing v), },
    { cases nat.le.dest (not_lt.mp hqn) with a ha,
      have hnaq : n=a+q := by linarith,
      simp [Hσφ_eq_neq_σδ hnaq (downgrade_vanishing v), neg_eq_zero],
      have eq := v.vanishing ⟨a, by linarith⟩ _, swap,
      { simp only [hnaq, fin.coe_mk, (show q.succ=q+1, by refl), add_assoc], },
      simp only [fin.succ_mk] at eq,
      simp only [← assoc, eq, zero_comp], }, },
end
  
lemma P_is_a_projector (q : ℕ) : (P q : (alternating_face_map_complex C).obj X ⟶ _) ≫ P q = P q :=
begin
  ext n,
  simp only [homological_complex.comp_f],
  cases n,
  { simp only [P_deg0_eq q, comp_id], },
  { exact P_is_identity_where_faces_vanish (higher_faces_vanish_P q n), },
end

/- construction of homotopies P q ~ id by induction on q -/


end dold_kan

end algebraic_topology

