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
import null_homotopic
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
#check hσ

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

def nat_trans_Hσ (q : ℕ) : ((alternating_face_map_complex C) ⟶
  (alternating_face_map_complex C)) :=
{ app := λ _, Hσ q,
  naturality' := λ X Y f,
  begin
    ext n,
    simp only [Hσ],
    cases n,
    { simp only [homological_complex.comp_f, chain_complex.of_hom_f],
      simp only [homotopy.null_homotopy_f_lower_end' (c_succ0) (c_lowerend)],
      sorry, },
    { sorry, },
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

variables {X Y : simplicial_object C}

end dold_kan

end algebraic_topology
