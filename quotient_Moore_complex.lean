/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import alternating_face_map_complex

open category_theory
open category_theory.limits
open category_theory.subobject
open category_theory.preadditive
open opposite

open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace degenerate_subcomplex

def σδ {C : Type*} [category C] {X : simplicial_object C}
  (q : ℕ) (n : ℕ) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1]))) :=
  X.δ (fin.mk (n-q+1) (nat.succ_lt_succ (nat.sub_lt_succ n q))) ≫
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

def π : ℕ → Π n : ℕ, (X.obj (op [n]) ⟶ (X.obj (op [n])))
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
def ν (q : ℕ) (n : ℕ) : (X.obj (op [n]) ⟶ (X.obj (op [n]))) := 𝟙 _ - π q n

@[simp]
lemma π0_eq (n : ℕ) :
  (π 0 n : (X.obj (op [n]) ⟶ (X.obj (op [n])))) = 𝟙 _ := by unfold π

@[simp]
lemma ν0_eq (n : ℕ) :
  (ν 0 n : (X.obj (op [n]) ⟶ (X.obj (op [n])))) = 0 :=
  by { unfold ν, rw π0_eq, rw [sub_self], }

@[simp]
lemma π_deg0_eq (q : ℕ) :
  (π q 0 : (X.obj (op [0]) ⟶ (X.obj (op [0])))) = 𝟙 _ :=
begin
  cases q,
  { exact π0_eq 0, },
  { unfold π, simp only [nat.rec_zero], },
end

@[simp]
lemma ν_deg0_eq (q : ℕ) :
  (ν q 0 : (X.obj (op [0]) ⟶ (X.obj (op [0])))) = 0 :=
by { unfold ν, simp only [π_deg0_eq, sub_self], }

@[simp]
lemma π_eq (q : ℕ) (n : ℕ) (hqn : q ≤ n) :
  (π (q+1) (n+1) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1])))) = 
  π q (n+1) ≫ (𝟙 _ - σδ q n) :=
by { unfold π, rw [nat.rec_add_one], split_ifs, refl, }

/- to https://leanprover-community.github.io/mathlib_docs/algebra/group/commute.html ? -/
@[simp]
lemma comm_group_trivial_lemma (α : Type*) [add_comm_group α] (a b c : α) :
  a - (b - c) = a - b + c := by
{ rw sub_eq_iff_eq_add, rw [add_add_sub_cancel, sub_add_cancel], }

@[simp]
lemma ν_eq (q : ℕ) (n : ℕ) (hqn : q ≤ n) :
  (ν (q+1) (n+1) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1])))) = 
  ν q (n+1) + (𝟙 _ - ν q (n+1)) ≫ σδ q n :=
begin
  unfold ν,
  rw π_eq q n hqn,
  simp only [comm_group_trivial_lemma, comp_sub, zero_add, category.comp_id, sub_self],
end

@[simp]
lemma π_eq' (q : ℕ) (n : ℕ) (hqn : n < q) :
  (π (q+1) (n+1) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1])))) = π q (n+1) :=
begin
  unfold π,
  rw [nat.rec_add_one],
  split_ifs,
  { exfalso, linarith, },
  { refl, }
end

@[simp]
lemma ν_eq' (q : ℕ) (n : ℕ) (hqn : n < q ) :
  (ν (q+1) (n+1) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1])))) = ν q (n+1) :=
by { unfold ν, rw [sub_right_inj], exact π_eq' q n hqn, }


/- the image of π q n is contained in N_q X_n -/

lemma d_π_eq_zero (q : ℕ) (n : ℕ) : ∀ (j : ℕ) (h1 : j+1 ≤ n+1) (h2 : n+1 ≤ j+q),
  (π q (n+1) ≫ X.δ (fin.mk (j+1) (by linarith)) : X.obj (op [n+1]) ⟶ (X.obj (op [n]))) = 0 :=
begin
  induction q with q hq,
  { intros j h1 h2,
    exfalso, linarith, },
  { intros j h1 h2,
    by_cases h3 : n<q,
    { rw π_eq' q n h3,
      exact hq j h1 (by linarith), },
    { rw not_lt at h3,
      rw π_eq q n h3,
      by_cases h4 : n+1 ≤ j+q,
      { simp only [comp_sub, sub_comp, category.comp_id, category.assoc, hq j h1 h4],
        simp only [zero_sub, neg_eq_zero],
        unfold σδ,
        simp, /- pour l'affichage -/
      sorry, },
      { sorry, }, }, },
end


/- what follows makes sense only in an abelian category -/

@[simp]
def obj_X {A : Type*} [category A] [abelian A] {Y : simplicial_object A} : Π n : ℕ, subobject (Y.obj(op(simplex_category.mk n)))
| 0 := ⊥ 
| (n+1) := finset.univ.sup (λ k : fin(n+1), subobject.mk (image.ι (Y.σ 0)))

end degenerate_subcomplex

end algebraic_topology
