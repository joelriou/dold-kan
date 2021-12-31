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

import dold_kan1

/-!

Goal : 
* show that a morphism of simplicial objects is an isomorphisms if and only if it
induces an isomorphism on normalized Moore complexes (TODO)

-/

open category_theory
open category_theory.limits
open category_theory.subobject
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.category
open homology
open opposite

open_locale big_operators
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

def hσ_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  (f.app (op (simplex_category.mk n)) ≫ hσ q n : X _[n] ⟶ Y _[n+1]) =
  hσ q n ≫ f.app (op (simplex_category.mk (n+1))) :=
begin
  by_cases hqn : n<q; unfold hσ; split_ifs,
  { simp only [zero_comp, comp_zero], },
  { simp only [zsmul_comp, comp_zsmul],
    apply congr_arg,
    erw f.naturality,
    refl, },
end

def hσ'_naturality (q n m : ℕ) (hnm : c.rel m n)
  {X Y : simplicial_object C} (f : X ⟶ Y) :
  (f.app (op (simplex_category.mk n)) ≫ hσ' q n m hnm) =
  hσ' q n m hnm ≫ f.app (op (simplex_category.mk m)) :=
begin
  simp only [hσ', ← assoc, hσ_naturality],
  have eq := f.naturality (eq_to_hom (show op [n+1] = op [m], by { congr, exact hnm, })),
  simp only [eq_to_hom_map] at eq,
  simp only [assoc, eq],
end

def nat_trans_Hσ (q : ℕ) : ((alternating_face_map_complex C) ⟶
  (alternating_face_map_complex C)) :=
{ app := λ _, Hσ q,
  naturality' := λ X Y f,
  begin
    ext n,
    simp only [Hσ],
    cases n,
    { simp only [homological_complex.comp_f,
        homotopy.null_homotopic_map'_f_of_not_rel_left c_succ0 c_lowerend, ← assoc],
      erw hσ'_naturality q 0 1 c_succ0,
      simp only [assoc, ← ((alternating_face_map_complex C).map f).comm,
        alternating_face_map_complex],
      simp only [chain_complex.of_hom_f, alternating_face_map_complex_map,
        alternating_face_map_complex.map], },
    { simp only [homological_complex.comp_f,
        homotopy.null_homotopic_map'_f (c_succ (n+1)) (c_succ n), comp_add, add_comp],
      rw ← assoc,
      erw [((alternating_face_map_complex C).map f).comm],
      conv { to_rhs, congr, skip, rw assoc, erw ← ((alternating_face_map_complex C).map f).comm, },
      conv { to_lhs, congr, rw assoc, skip, rw ← assoc, },
      erw hσ'_naturality q n (n+1) (c_succ n),
      erw hσ'_naturality q (n+1) (n+2) (c_succ (n+1)),
      simp only [chain_complex.of_hom_f, assoc, alternating_face_map_complex_map,
        alternating_face_map_complex.map], },
  end}

def nat_trans_P (q : ℕ) : ((alternating_face_map_complex C) ⟶
  (alternating_face_map_complex C)) :=
{ app := λ _, P q,
  naturality' := λ X Y f,
  begin
    induction q with q hq,
    { simp only [P, id_comp, comp_id], },
    { unfold P,
      simp only [add_comp, comp_add, assoc, comp_id],
      rw hq,
      apply congr_arg,
      rw [← assoc, hq, assoc],
      apply congr_arg,
      exact (nat_trans_Hσ q).naturality' f, }
  end }

def P_termwise_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
   f.app (op [n]) ≫ (P q).f n = (P q).f n ≫ f.app (op [n]) :=
congr_arg ((λ g, g.f n) : (((alternating_face_map_complex C).obj X) ⟶
  ((alternating_face_map_complex C).obj Y)) → (_ ⟶ _ ))
  ((nat_trans_P q).naturality f)

/- TODO, P q vanishes on the q higher degeneracies -/

@[ext]
structure morph_components (X : simplicial_object C) (n : ℕ) (Z : C) :=
  (a : X _[n+1] ⟶ Z) (b : fin(n+1) → (X _[n] ⟶ Z))

def F {Z : C} {n : ℕ} {X : simplicial_object C} (f : morph_components X n Z) : X _[n+1] ⟶ Z :=
  P_infty.f (n+1) ≫ f.a + ∑ (i : fin (n+1)), (((P i).f (n+1)) ≫ (X.δ i) ≫ (f.b i)) 

def morph_components_comp {X : simplicial_object C} {n : ℕ} {Z Z' : C}
  (f : morph_components X n Z) (g : Z ⟶ Z') : morph_components X n Z' :=
{ a := f.a ≫ g,
  b := λ i, f.b i ≫ g }

lemma F_comp {X : simplicial_object C} {n : ℕ} {Z Z' : C} (f : morph_components X n Z)
  (g : Z ⟶ Z') : F (morph_components_comp f g) = F f ≫ g :=
begin
  unfold F morph_components_comp,
  simp only [add_comp, sum_comp, assoc],
end

def comp_morph_components {X' X : simplicial_object C} {n : ℕ} {Z : C}
  (g : X' ⟶ X) (f : morph_components X n Z) : morph_components X' n Z :=
{ a := g.app (op [n+1]) ≫ f.a,
  b := λ i, g.app (op [n]) ≫ f.b i }

lemma comp_F {X' X : simplicial_object C} {n : ℕ} {Z : C}
  (g : X' ⟶ X) (f : morph_components X n Z) :
  F (comp_morph_components g f) = g.app (op [n+1]) ≫ F f :=
begin
  unfold F comp_morph_components,
  simp only [P_infty_termwise, comp_add],
  congr' 1,
  { simp only [← assoc, P_termwise_naturality], },
  { simp only [comp_sum],
    congr,
    ext,
    slice_rhs 1 2 {rw P_termwise_naturality, },
    slice_lhs 2 3 {erw g.naturality, },
    simp only [assoc],
    refl, }
end

def morph_components_id (X : simplicial_object C) (n : ℕ) :
  morph_components X n (X _[n+1]) :=
{ a := P_infty.f (n+1),
  b := λ i, X.σ i, }

lemma F_id (X : simplicial_object C) (n : ℕ) :
  F (morph_components_id X n) = 𝟙 _ :=
begin
  sorry
end

theorem normalized_Moore_complex_reflects_iso {X Y : simplicial_object C}
  (f : X ⟶ Y) (g : Y ⟶ X)
  (hgf : P_infty ≫ alternating_face_map_complex.map (f ≫ g) ≫ P_infty = 𝟙 _)
  (hgf : P_infty ≫ alternating_face_map_complex.map (f ≫ g) ≫ P_infty = 𝟙 _)
  (n : ℕ) : 0 = 0 :=
  begin
    have foo := P_infty ≫ alternating_face_map_complex.map (f ≫ g) ≫ P_infty,
    sorry,
  end

variables {X Y : simplicial_object C}

end dold_kan

end algebraic_topology
