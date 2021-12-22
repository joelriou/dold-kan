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
the endomorphism ν q n : X_n → X_n is meant to be the projector
with image a subcomplex D_q and kernel N_q, where
N_q X_n is the intersection of the diffentials       δ_j : K_n → K_{n-1} for j>n-q & j>0
D_q X_n is the sum of the images of the degeneracies σ_i : K_{n-1} → K_n for j≥n-q

This shall be checked in the case when the category is abelian, but the definition
of the projectors makes sense even if the category is preadditive only.
-/

def ν : ℕ → Π n : ℕ, (X.obj (op [n]) ⟶ (X.obj (op [n])))
| 0     := λ n, 0
| (q+1) := λ n,
  begin
    cases n,
    { exact 0, },
    { exact if q ≤ n
        then ν q (n+1) ≫ (𝟙 _ - σδ q n)
        else ν q (n+1), },
  end

/-- π are the complement projectors of the ν -/
def π (q : ℕ) (n : ℕ) : (X.obj (op [n]) ⟶ (X.obj (op [n]))) := 𝟙 _ - ν q n

@[simp]
lemma ν0_eq (n : ℕ) :
  (ν 0 n : (X.obj (op [n]) ⟶ (X.obj (op [n])))) = 0 :=
begin
  unfold ν,
end

@[simp]
lemma ν_eq (q : ℕ) (n : ℕ) (hqn : q ≤ n) :
  (ν (q+1) (n+1) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1])))) = 
  ν q (n+1) ≫ (𝟙 _ - σδ q n) :=
begin
  unfold ν,
  rw [nat.rec_add_one],
  split_ifs,
  refl,
end

@[simp]
lemma ν_eq' (q : ℕ) (n : ℕ) (hqn : n < q ) :
  (ν (q+1) (n+1) : (X.obj (op [n+1]) ⟶ (X.obj (op [n+1])))) = ν q (n+1) :=
begin
  unfold ν,
  rw [nat.rec_add_one],
  split_ifs,
  { exfalso, linarith, },
  { refl, }
end




/- what follows makes sense only in an abelian category -/

@[simp]
def obj_X {A : Type*} [category A] [abelian A] {Y : simplicial_object A} : Π n : ℕ, subobject (Y.obj(op(simplex_category.mk n)))
| 0 := ⊥ 
| (n+1) := finset.univ.sup (λ k : fin(n+1), subobject.mk (image.ι (Y.σ 0)))

end degenerate_subcomplex

end algebraic_topology
