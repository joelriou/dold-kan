/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.homotopies

open category_theory
open category_theory.category
open category_theory.preadditive
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

lemma remove_trailing_zeros_in_sum {β : Type*} [add_comm_monoid β] {n a q : ℕ}
  (hnaq : n=a+q) (f : fin(n) → β)
  (hf : ∀ (j : fin(q)), f (translate_fin a hnaq j) = 0) :
  ∑ (i : fin(n)), f i =
  ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ, f i :=
begin
  rw ← finset.sum_filter_of_ne _,
  intros i h₀ h₁,
  by_contradiction h₂,
  apply h₁,
  cases nat.le.dest (not_lt.mp h₂) with j hj,
  have h₃ := hf ⟨j, _⟩, swap,
  { apply (add_lt_add_iff_left a).mp,
    rw [← hnaq, hj],
    exact fin.is_lt i, },
  simp only [hj, translate_fin, fin.eta, fin.coe_mk] at h₃,
  exact h₃,
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
  have ineq1 : a<n+1 := nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq)),
  have ineq2 : a+1<n+2 := nat.succ_lt_succ ineq1,
  let term1 := λ (j : fin(n+2)), ((-1 : ℤ)^(j : ℕ) * (-1 : ℤ)^a) •
    (φ ≫ X.δ j) ≫ X.σ ⟨a, ineq1⟩,
  let term2 := λ (j : fin(n+3)), ((-1 : ℤ)^(a+1) * (-1 : ℤ)^(j : ℕ)) •
    (φ ≫ X.σ ⟨a+1, ineq2⟩) ≫ X.δ j,
  simp only [← term1, ← term2],
  sorry
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
