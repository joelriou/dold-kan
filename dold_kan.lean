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

/- general stuff on homotopies -/

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

variables {X : simplicial_object C}

def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] := if n<q then 0
  else (-1 : ℤ)^(n-q) • X.σ (fin.mk (n-q) (nat.sub_lt_succ n q))

@[simp]
lemma hσ_eq_zero (q : ℕ) (n : ℕ) (hnq : n<q) : (hσ q n : X _[n] ⟶ X _[n+1])= 0 :=
begin
  unfold hσ,
  simp only [fin.mk_eq_subtype_mk, ite_eq_left_iff],
  intro h,
  exfalso,
  exact h hnq,
end

@[simp]
lemma hσ_eq (q n a : ℕ) (ha : a+q=n) :
  (hσ q n : X _[n] ⟶ X _[n+1]) = (-1 : ℤ)^a • X.σ (fin.mk a (nat.lt_succ_iff.mpr (nat.le.intro ha))) :=
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
      simp [hσ_eq 0 0 0 (by refl), alternating_face_map_complex.obj_d],
      rw [fin.sum_univ_succ_above, fin.sum_univ_one,
        fin.zero_succ_above, fin.succ_zero_eq_one],
      simp only [comp_neg, fin.coe_zero, comp_add, fin.coe_one, pow_one,
        one_zsmul, pow_zero, neg_smul],
      apply add_neg_eq_zero.mpr,
      erw [δ_comp_σ_self, δ_comp_σ_succ], },
    { simp, }, },
end

/- vanishing of some faces -/

structure higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
  (vanishing : ∀ (j : fin(n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0)

lemma Hσφ_eq_zero {Y : C} {n : ℕ} (q : ℕ) (hqn : q<n) (φ : Y ⟶ X _[n+1])
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 := sorry

lemma Hσφ_eq_σδ {Y : C} {n : ℕ} (q : ℕ) (hqn : q≤n) (φ : Y ⟶ X _[n+1])
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 
  φ ≫ X.δ (fin.mk (n-q) (nat.sub_lt_succ n q)).succ ≫
  X.σ (fin.mk (n-q) (nat.sub_lt_succ n q)) := sorry

lemma higher_faces_vanish_ind {Y : C} {n : ℕ} (q : ℕ) {φ : Y ⟶ X _[n+1]} 
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ - Hσ q).f (n+1)) :=
{ vanishing :=
  begin
      sorry
  end
}

end dold_kan

end algebraic_topology

