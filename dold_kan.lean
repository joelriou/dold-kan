/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebra.homology.homotopy
import algebra.big_operators.basic
import algebraic_topology.simplicial_object
import alternating_face_map_complex

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

namespace degenerate_subcomplex

def σδ {C : Type*} [category C] {X : simplicial_object C}
  (q : ℕ) (n : ℕ) : X _[n+1] ⟶ X _[n+1] :=
  X.δ (fin.mk (n-q) (nat.sub_lt_succ n q)).succ ≫
  X.σ (fin.mk (n-q) (nat.sub_lt_succ n q))

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

/-- Given a simplicial object X in an abelian category,
the endomorphism π q n : X_n → X_n is meant to be the projector
with image N_q and kernel D_q, where
N_q X_n is the intersection of the diffentials       δ_j : K_n → K_{n-1} for j>n-q & j>0
D_q X_n is the sum of the images of the degeneracies σ_i : K_{n-1} → K_n for j≥n-q

This shall be checked in the case when the category is abelian, but the definition
of the projectors makes sense even if the category is preadditive only.
-/

def π : ℕ → Π n : ℕ, X _[n] ⟶ X _[n]
| 0     := λ n, 𝟙 _
| (q+1) := λ n,
  begin
    cases n,
    { exact 𝟙 _, },
    { exact if q ≤ n
        then π q (n+1) ≫ (𝟙 _ - σδ q n)
        else π q (n+1), },
  end

/-- ν are the complement projectors of the π -/
def ν (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n] := 𝟙 _ - π q n

@[simp]
lemma π0_eq (n : ℕ) :
  (π 0 n : X _[n] ⟶ X _[n]) = 𝟙 _ := by unfold π

@[simp]
lemma ν0_eq (n : ℕ) :
  (ν 0 n : X _[n] ⟶ X _[n]) = 0 :=
  by { unfold ν, rw π0_eq, rw [sub_self], }

@[simp]
lemma π_deg0_eq (q : ℕ) :
  (π q 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  cases q,
  { exact π0_eq 0, },
  { unfold π, simp only [nat.rec_zero], },
end

@[simp]
lemma ν_deg0_eq (q : ℕ) :
  (ν q 0 : X _[0] ⟶ X _[0]) = 0 :=
by { unfold ν, simp only [π_deg0_eq, sub_self], }

@[simp]
lemma π_eq (q : ℕ) (n : ℕ) (hqn : q ≤ n) :
  (π (q+1) (n+1) : X _[n+1] ⟶ X _[n+1]) = 
  π q (n+1) ≫ (𝟙 _ - σδ q n) :=
by { unfold π, rw [nat.rec_add_one], split_ifs, refl, }

/- to https://leanprover-community.github.io/mathlib_docs/algebra/group/commute.html ? -/
@[simp]
lemma comm_group_trivial_lemma (α : Type*) [add_comm_group α] (a b c : α) :
  a - (b - c) = a - b + c := by
{ rw [sub_eq_iff_eq_add, add_add_sub_cancel, sub_add_cancel], }

@[simp]
lemma ν_eq (q : ℕ) (n : ℕ) (hqn : q ≤ n) :
  (ν (q+1) (n+1) : X _[n+1] ⟶ X _[n+1]) = 
  ν q (n+1) + (𝟙 _ - ν q (n+1)) ≫ σδ q n :=
begin
  unfold ν,
  rw π_eq q n hqn,
  simp only [comm_group_trivial_lemma, comp_sub, zero_add, category.comp_id, sub_self],
end

@[simp]
lemma π_eq' (q : ℕ) (n : ℕ) (hqn : n < q) :
  (π (q+1) (n+1) : X _[n+1] ⟶ X _[n+1]) = π q (n+1) :=
begin
  unfold π,
  rw [nat.rec_add_one],
  split_ifs,
  { exfalso, linarith, },
  { refl, }
end

@[simp]
lemma ν_eq' (q : ℕ) (n : ℕ) (hqn : n < q ) :
  (ν (q+1) (n+1) : X _[n+1] ⟶ X _[n+1]) = ν q (n+1) :=
by { unfold ν, rw [sub_right_inj], exact π_eq' q n hqn, }


/- the image of π q n is contained in N_q X_n -/

lemma d_π_eq_zero (q : ℕ) (n : ℕ) : ∀ (j : fin(n+1)) (hj : n+1 ≤ (j : ℕ)+q),
  (π q (n+1) ≫ X.δ j.succ : X _[n+1] ⟶ X _[n]) = 0 :=
begin
  induction q with q hq,
  { intros j hj,
    have h1 := fin.is_lt j,
    exfalso, linarith, },
  { intros j hj,
    have h1 := fin.is_lt j,
    by_cases h2 : n<q,
    { rw π_eq' q n h2,
      exact hq j (by linarith), },
    { rw not_lt at h2,
      rw π_eq q n h2,
      by_cases h3 : n+1 ≤ (j : ℕ)+q,
      { simp only [comp_sub, sub_comp, category.comp_id, category.assoc, hq j h3],
        simp only [zero_sub, neg_eq_zero],
        unfold σδ,
        cases (nat.le.dest h2) with a ha,
        rw eq_comm at ha,
        simp only [ha] at h3,
        have eq : n - q = a := by linarith,
        simp only [eq],
        cases n with m hm,
        { simp only [show a=0, by linarith, show j=0, by linarith,
            fin.mk_zero, fin.mk_eq_subtype_mk, fin.mk_one],
          slice_lhs 1 2 { erw hq (0 : fin(1)) (by linarith)},
          simp only [zero_comp], },
        { have ineq1 : fin.cast_succ (fin.mk a (show a<m.succ, by linarith)) < j, 
          { rw [fin.lt_iff_coe_lt_coe],
            simp only [fin.mk_eq_subtype_mk, fin.cast_succ_mk, fin.coe_mk],
            linarith, },
          slice_lhs 3 4 { erw δ_comp_σ_of_gt X ineq1, },
          have ineq2 : (fin.mk (a+1) (show a+1<m.succ+1, by linarith)) ≤ j,
          { rw [fin.le_iff_coe_le_coe],
            simp only [fin.mk_eq_subtype_mk, fin.coe_mk],
            linarith, },
          slice_lhs 2 3 { erw ← δ_comp_δ X ineq2, },
          slice_lhs 1 2 { erw hq j (by linarith), },
          simp only [zero_comp], }, },
      { rw [show q.succ = q+1, by refl] at hj,
        have eq : n-q = j := by linarith,
        clear h2 h3 h1 hj,
        simp only [comp_sub, sub_comp],
        rw sub_eq_zero,
        repeat { rw assoc, },
        apply whisker_eq,
        simp only [id_comp],
        unfold σδ,
        simp only [eq],
        simp only [fin.mk_eq_subtype_mk, fin.eta],
        slice_rhs 2 3 { erw δ_comp_σ_succ X, },
        simp only [comp_id], }, }, },
end

lemma d_ν_eq_zero (q : ℕ) (n : ℕ) (j : fin(n+1)) (hj : n+1 ≤ (j : ℕ)+q) :
  (ν q (n+1) ≫ X.δ j.succ : X _[n+1] ⟶ X _[n]) = X.δ j.succ :=
begin
  unfold ν,
  rw [sub_comp, d_π_eq_zero q n j hj, sub_zero, id_comp],
end

/- general stuff of homotopies -/

@[simp]
def null_homotopic_chain_complex_map_f {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) : Π (n : ℕ), K.X n ⟶ L.X n
| 0 := h 0 ≫ L.d 1 0
| (n+1) := h (n+1) ≫ L.d (n+2) (n+1) + K.d (n+1) n ≫ h n

@[simps]
def null_homotopic_chain_complex_map {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) : K ⟶ L :=
{ f := null_homotopic_chain_complex_map_f h,
  comm' := λ i j, begin
    rw complex_shape.down_rel,
    intro hij,
    cases j;
    { rw ← hij, simp, },
  end }

@[simp]
def null_homotopic_chain_complex_map_hom {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) (i j : ℕ) : K.X i ⟶ L.X j :=
begin
  by_cases hij : i+1=j,
  { exact h i ≫ (eq_to_hom (by { congr, assumption, }) : L.X (i+1) ⟶ L.X j) },
  { exact 0 },
end

def homotopy_of_null_homotopic_chain_complex_map {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) :
  homotopy (null_homotopic_chain_complex_map h) 0 :=
{ hom := null_homotopic_chain_complex_map_hom h,
  zero' := λ i j hij, begin
    rw complex_shape.down_rel at hij,
    simp only [null_homotopic_chain_complex_map_hom, dite_eq_right_iff],
    intro hij',
    exfalso,
    exact hij hij',
  end,
  comm := λ n, begin
    cases n,
    { simp, },
    { simp, apply add_comm, }
  end }

/- construction of homotopies -/

def hσδ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] :=
  if n<q
  then 0
  else (-1 : ℤ)^(n-q) • X.σ (fin.mk (n-q) (nat.sub_lt_succ n q))

@[simp]
lemma hσδ_eq_zero (q : ℕ) (n : ℕ) (hnq : n<q) : (hσδ q n : X _[n] ⟶ X _[n+1])= 0 :=
begin
  unfold hσδ,
  simp only [fin.mk_eq_subtype_mk, ite_eq_left_iff],
  intro h,
  exfalso,
  exact h hnq,
end

@[simp]
lemma hσδ_eq (q n a : ℕ) (ha : a+q=n) :
  (hσδ q n : X _[n] ⟶ X _[n+1]) = (-1 : ℤ)^a • X.σ (fin.mk a (nat.lt_succ_iff.mpr (nat.le.intro ha))) :=
begin
  unfold hσδ,
  simp only [not_lt, fin.mk_eq_subtype_mk, ite_eq_left_iff],
  split_ifs,
  { exfalso, linarith, },
  { congr; exact tsub_eq_of_eq_add (eq.symm ha), }
end

@[simp]
def Hσδ (q : ℕ) : (alternating_face_map_complex C).obj X ⟶
  (alternating_face_map_complex C).obj X :=
null_homotopic_chain_complex_map (hσδ q)

lemma Hσδ_eq {Y : C} (q : ℕ) (n : ℕ) (hqn : q≤n) (φ : Y ⟶ X _[n+1]) 
  (hφ : ∀ (j : fin(n+1)), (n+1 ≤ (j : ℕ)+q) → φ ≫ X.δ j.succ = 0) :
  φ ≫ ((Hσδ q).f (n+1) : X _[n+1] ⟶ X _[n+1]) = φ ≫ σδ q n :=
begin
  sorry,
end


@[simp]
def P : ℕ → ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X)
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ - Hσδ q)

theorem P_eq_π (q : ℕ) (n : ℕ) : ((P q).f n : X _[n] ⟶ X _[n]) = π q n :=
begin
  induction q with q hq,
  { simpa only [π0_eq, homological_complex.id_f, P], },
  { simp only [homological_complex.sub_f_apply, homological_complex.comp_f,
      comp_sub, P, comp_id, hq],
    cases n,
    { simp only [sub_eq_self, π_deg0_eq],
      erw id_comp,
      cases q,
      { simp,
        erw chain_complex.of_d,
        simp only [alternating_face_map_complex.obj_d, hσδ_eq 0 0 0 (by refl),
          fin.mk_zero, fin.mk_eq_subtype_mk, one_zsmul, pow_zero],
        rw [fin.sum_univ_succ_above, fin.sum_univ_one,
          fin.zero_succ_above, fin.succ_zero_eq_one],
        simp only [comp_neg, fin.coe_zero, comp_add, fin.coe_one, pow_one,
          one_zsmul, pow_zero, neg_smul],
        apply add_neg_eq_zero.mpr,
        erw [δ_comp_σ_self, δ_comp_σ_succ], },
      { simp, }, },
    { by_cases hqn : q≤n,
      { erw Hσδ_eq q n hqn (π q n.succ : X _[n+1] ⟶ X _[n+1]) (d_π_eq_zero q n),
        rw π_eq q n hqn,
        rw [comp_sub, comp_id], },
      { rw not_le at hqn,
        rw π_eq' q n hqn,
        apply sub_eq_self.mpr,
        simp [Hσδ],
        rw hσδ_eq_zero q n hqn,
        by_cases hqn1 : n+1<q,
        { rw hσδ_eq_zero q (n+1) hqn1,
          simp, },
        { rw [show q = n+1, by linarith],
          simp,
          apply sub_eq_zero.mpr,
          sorry, },
      }, }, },
end

/- what follows makes sense only in an abelian category -/

@[simp]
def obj_X {A : Type*} [category A] [abelian A] {Y : simplicial_object A} : Π n : ℕ, subobject (Y _[n])
| 0 := ⊥ 
| (n+1) := finset.univ.sup (λ k : fin(n+1), subobject.mk (image.ι (Y.σ 0)))

end degenerate_subcomplex

end algebraic_topology

