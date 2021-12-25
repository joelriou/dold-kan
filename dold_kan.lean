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
  else (-1 : ℤ)^(n-q) • X.σ (fin.mk (n-q) (nat.sub_lt_succ n q))

@[simp]
lemma hσ_eq_zero {q : ℕ} {n : ℕ} (hnq : n<q) : (hσ q n : X _[n] ⟶ X _[n+1])= 0 :=
begin
  unfold hσ,
  simp only [fin.mk_eq_subtype_mk, ite_eq_left_iff],
  intro h,
  exfalso,
  exact h hnq,
end

@[simp]
lemma hσ_eq {q n a : ℕ} (ha : a+q=n) : (hσ q n : X _[n] ⟶ X _[n+1]) =
    (-1 : ℤ)^a • X.σ (fin.mk a (nat.lt_succ_iff.mpr (nat.le.intro ha))) :=
begin
  unfold hσ,
  simp only [not_lt, fin.mk_eq_subtype_mk, ite_eq_left_iff],
  split_ifs,
  { exfalso, linarith, },
  { congr; exact tsub_eq_of_eq_add (eq.symm ha), }
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

/- these endormorphismes P q coincide with `𝟙` in degree 0 -/

lemma P_deg0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  induction q with q hq,
  { simp, },
  { simp [hq],
    cases q,
    { erw chain_complex.of_d,
      simp [hσ_eq (show 0+0=0, by refl), alternating_face_map_complex.obj_d],
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
fin.mk (a+(i:ℕ)) (gt_of_ge_of_gt (eq.ge hnaq) ((add_lt_add_iff_left a).mpr (fin.is_lt i)))

lemma remove_trailing_zero_in_sum {β : Type*} [add_comm_monoid β] {n : ℕ} {a : ℕ} {q : ℕ} (hnaq : n=a+q)
  {f : fin(n) → β} (hf : ∀ (j : fin(q)), f (translate_fin a hnaq j) = 0) :
  ∑ (i : fin(n)), f i = ∑ (i : fin(a)), f (fin.cast_le (nat.le.intro (eq.symm hnaq)) i) := 
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
      have hfj := hf (fin.mk j hjq),
      simp [hj] at hfj,
      exact hi2 hfj, }, },
  simp only [← finset.sum_filter_of_ne vanishing],
  apply eq.symm,
  let φ : Π (i : fin(a)), i ∈ (finset.univ : finset(fin(a))) → fin(n) :=
    λ i _, fin.cast_le (nat.le.intro (eq.symm hnaq)) i,
  apply finset.sum_bij φ,
  { intros i hi,
    simp only [true_and, finset.mem_univ, finset.mem_filter, φ, lt_a,
      fin.coe_cast_le],
    exact fin.is_lt i, },
  { intros i hi,
    congr, },
  { intros i j hi hj hij,
    simp only [φ] at hij,
    simpa only [order_embedding.eq_iff_eq] using hij, },
  { intros j hj,
    simp only [true_and, finset.mem_univ, finset.mem_filter, lt_a] at hj,
    let i : fin(a) := fin.mk (j:ℕ) hj,
    use [fin.mk (j:ℕ) hj, finset.mem_univ _],
    simp only [φ, fin.cast_le_mk, fin.mk_eq_subtype_mk, fin.eta], },
end

lemma Hσφ_eq_zero {Y : C} {n : ℕ} (q : ℕ) (hqn : n<q) (φ : Y ⟶ X _[n+1])
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  by_cases hqnp : n+1<q,
  { simp [Hσ],
    rw [hσ_eq_zero hqn, hσ_eq_zero hqnp],
    simp only [add_zero, zero_comp, comp_zero], },
  { have eqq := le_antisymm (not_lt.mp hqnp) (nat.succ_le_iff.mpr hqn),
    simp,
    rw hσ_eq (show 0+q=n+1, by linarith),
    simp only [fin.mk_zero, fin.mk_eq_subtype_mk, one_zsmul, pow_zero],
    erw chain_complex.of_d,
    simp only [alternating_face_map_complex.obj_d,
      hσ_eq_zero hqn, add_zero, comp_zero, comp_sum],
    have h2 : n+3=2+(n+1) := by linarith,
    rw [remove_trailing_zero_in_sum h2],
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

lemma Hσφ_eq_σδ {Y : C} {n : ℕ} (q : ℕ) (hqn : q≤n) (φ : Y ⟶ X _[n+1])
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 
  φ ≫ X.δ (fin.mk (n-q) (nat.sub_lt_succ n q)).succ ≫
  X.σ (fin.mk (n-q) (nat.sub_lt_succ n q)) :=
begin
  cases nat.le.dest hqn with a ha,
  have hnaq : a+q=n := by linarith,
  have hnaqsucc : (a+1)+q=n+1 := by linarith,
  simp [hσ_eq hnaq, hσ_eq hnaqsucc],
  repeat { erw chain_complex.of_d, },
  simp only [alternating_face_map_complex.obj_d, comp_sum, sum_comp],
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul],
  sorry,
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

