/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import homotopy
--import algebra.homology.homotopy
import algebra.big_operators.basic
import algebraic_topology.simplicial_object
import algebraic_topology.alternating_face_map_complex

import dold_kan1

/-!

Goal : 
* show that a morphism of simplicial objects is an isomorphisms if and only if it
induces an isomorphism on normalized Moore complexes

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

lemma hσ_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
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

lemma hσ'_naturality (q n m : ℕ) (hnm : c.rel m n)
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
        homotopy.null_homotopic_map_f_of_not_rel_left c_succ0 c_lowerend, ← assoc],
      erw hσ'_naturality q 0 1 c_succ0,
      simp only [assoc, ← ((alternating_face_map_complex C).map f).comm,
        alternating_face_map_complex],
      simp only [chain_complex.of_hom_f, alternating_face_map_complex_map,
        alternating_face_map_complex.map], },
    { simp only [homological_complex.comp_f,
        homotopy.null_homotopic_map_f (c_succ (n+1)) (c_succ n), comp_add, add_comp],
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

lemma P_termwise_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
   f.app (op [n]) ≫ (P q).f n = (P q).f n ≫ f.app (op [n]) :=
congr_arg ((λ g, g.f n) : (((alternating_face_map_complex C).obj X) ⟶
  ((alternating_face_map_complex C).obj Y)) → (_ ⟶ _ ))
  ((nat_trans_P q).naturality f)

@[ext]
structure morph_components (X : simplicial_object C) (n : ℕ) (Z : C) :=
  (a : X _[n+1] ⟶ Z) (b : fin(n+1) → (X _[n] ⟶ Z))

def reverse_fin {n : ℕ} (i : fin(n+1)) : fin(n+1):= ⟨n-i, nat.sub_lt_succ n ↑i⟩

lemma reverse_fin_eq {n a : ℕ} (i : fin(n+1)) (hnaq : n=a+i) : reverse_fin i = 
  ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
begin
  ext,
  simp only [reverse_fin, fin.coe_mk],
  exact tsub_eq_of_eq_add hnaq,
end

def F {Z : C} {n : ℕ} {X : simplicial_object C} (f : morph_components X n Z) :
  X _[n+1] ⟶ Z :=
  P_infty.f (n+1) ≫ f.a + ∑ (i : fin (n+1)),
  (((P i).f (n+1)) ≫ (X.δ (reverse_fin i).succ) ≫ (f.b (reverse_fin i))) 

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

def Q {X : simplicial_object C} (q : ℕ) : ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X) := 𝟙 _ - P q

lemma decomposition_Q {X : simplicial_object C} (n q : ℕ) (hqn : q≤n+1) :
  ((Q q).f (n+1) : X _[n+1] ⟶ X _[n+1]) =
  ∑ (i : fin(n+1)) in finset.filter (λ i : fin(n+1), (i:ℕ)<q) finset.univ,
    (P i).f (n+1) ≫ X.δ (reverse_fin i).succ ≫ X.σ (reverse_fin i) :=
begin
  revert hqn,
  induction q with q hq,
  { intro hqn,
    simp only [Q, P, nat.not_lt_zero, finset.sum_empty, finset.filter_false,
      homological_complex.zero_f_apply, sub_self], },
  { intro hqn,
    rw [leave_out_last_term (nat.succ_le_iff.mp hqn), ← hq (nat.le_of_succ_le hqn)],
    cases nat.le.dest (nat.succ_le_succ_iff.mp hqn) with a ha,
    let i : fin(n+1) := ⟨q,nat.lt_succ_iff.mpr (nat.le.intro ha)⟩,
    simp only [fin.succ_mk, fin.coe_mk, norm_num.sub_nat_pos n q a ha,
      reverse_fin_eq i (show n=a+i, by { simp only [fin.coe_mk, add_comm, ha], })],
    have eq : ((_ : X _[n+1] ⟶ _) = _ ) := eq_neg_of_eq_neg 
      (Hσφ_eq_neg_σδ (show n=a+q, by linarith) (higher_faces_vanish_P q n)),
    rw eq,
    unfold Q P,
    simp only [homological_complex.sub_f_apply, comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, homological_complex.id_f, comp_id],
    abel,
  },
end

lemma F_id (X : simplicial_object C) (n : ℕ) :
  F (morph_components_id X n) = 𝟙 _ :=
begin
  dsimp [comp_morph_components, morph_components_id, F],
  simp only [P_infty_termwise],
  rw [← homological_complex.comp_f, P_is_a_projector (n+1)],
  rw [show 𝟙 (X.obj (op [n + 1])) = (P (n+1)).f (n+1)+(Q (n+1)).f (n+1), by
  { unfold Q, simp only [homological_complex.sub_f_apply, add_sub_cancel'_right,
    homological_complex.id_f], refl, }],
  congr,
  rw decomposition_Q n (n+1) rfl.ge,
  congr,
  ext,
  simp only [true_and, true_iff, finset.mem_univ, finset.mem_filter, fin.is_lt],
end

theorem normalized_Moore_complex_reflects_iso {X Y : simplicial_object C}
  (f : X ⟶ Y) (g : alternating_face_map_complex.obj Y ⟶ alternating_face_map_complex.obj X)
  (hgf : P_infty ≫ alternating_face_map_complex.map f ≫ g = P_infty)
  (hfg : P_infty ≫ g ≫ alternating_face_map_complex.map f = P_infty) : is_iso f :=
  begin
    /- restating the result in a way that allows induction on the degree n -/
    haveI : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (f.app Δ), swap,
    { exact nat_iso.is_iso_of_is_iso_app f, },
    intro s,
    let m := simplex_category.len (unop s),
    rw [show s = op [m], by { simp only [op_unop, simplex_category.mk_len], }],
    generalize : m = n,
    /- from the assumptions hgf & hfg, we can get degreewise identities of morphisms in C
      using congr_arg (proj n _ _) -/
    let proj : Π (n : ℕ) (A B : chain_complex C ℕ) (f : A ⟶ B), A.X n ⟶ B.X n := λ n A B f, f.f n,
    /- we have to construct an inverse to f in degree n, by induction on n -/
    induction n with n hn,
    /- degree 0 -/
    { use g.f 0,
      split,
      { have eq := congr_arg (proj 0 _ _) hgf,
        simpa only [proj, homological_complex.comp_f, chain_complex.of_hom_f,
          alternating_face_map_complex.map, P_infty_termwise,
          P_deg0_eq, id_comp] using eq, },
      { have eq := congr_arg (proj 0 _ _) hfg,
        simpa only [proj, homological_complex.comp_f, chain_complex.of_hom_f,
          homological_complex.id_f, alternating_face_map_complex.map, P_infty_termwise,
          P_deg0_eq, id_comp] using eq, }, },
    /- isomorphism in degree n+1 of an isomorphism in degree n -/
    { resetI,
      let γ : morph_components Y n (X _[n+1]) :=
      { a := P_infty.f (n+1) ≫ g.f (n+1),
        b := λ i, inv (f.app (op [n])) ≫ X.σ i, },
      use F γ,
      split,
      { rw [← comp_F, ← F_id],
        congr,
        dsimp [comp_morph_components, morph_components_id],
        ext,
        { have eq := congr_arg (proj (n+1) _ _) hgf,
          simp only [proj, homological_complex.comp_f, chain_complex.of_hom_f,
          alternating_face_map_complex.map, P_infty_termwise] at eq ⊢,
          rw [← assoc] at eq ⊢,
          simpa only [← P_termwise_naturality] using eq, },
        { simp only [is_iso.hom_inv_id_assoc], }, },
      { rw [← F_comp, ← F_id],
        congr,
        dsimp [morph_components_comp, morph_components_id],
        ext,
        { have eq := congr_arg (proj (n+1) _ _) hfg,
          simpa only [proj, homological_complex.comp_f, chain_complex.of_hom_f,
          alternating_face_map_complex.map, P_infty_termwise, assoc] using eq, },
        { simp only [assoc],
          erw f.naturality,
          simp only [is_iso.inv_hom_id_assoc],
          refl, }, }, },
  end

end dold_kan

end algebraic_topology
