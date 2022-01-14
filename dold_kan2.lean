/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebra.homology.homotopy
import algebra.big_operators.basic
import algebraic_topology.alternating_face_map_complex
import category_theory.pseudoabelian.basic
import category_theory.pseudoabelian.simplicial_object

import dold_kan1

/-!

Goal : 
* show that a morphism of simplicial objects is an isomorphisms if and only if it
induces an isomorphism on normalized Moore complexes,
this is `normalized_Moore_complex_reflects_iso`

-/

open category_theory
open category_theory.limits
open category_theory.subobject
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.category
open category_theory.pseudoabelian
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
    congr' 1,
    erw f.naturality,
    refl, },
end

lemma hσ'_naturality (q : ℕ) (ij : homotopy.set_of_cs c)
  {X Y : simplicial_object C} (f : X ⟶ Y) :
  (f.app (op (simplex_category.mk ij.val.1))) ≫ hσ' q ij =
  hσ' q ij ≫ f.app (op (simplex_category.mk ij.val.2)) :=
begin
  simp only [hσ', ← assoc, hσ_naturality],
  have eq := f.naturality (eq_to_hom (show op [ij.val.1+1] = op [ij.val.2], by { congr, exact ij.property, })),
  simp only [eq_to_hom_map] at eq,
  simp only [assoc, eq],
end

/-- For each q, Hσ q is a natural transformation. -/
def nat_trans_Hσ (q : ℕ) : ((alternating_face_map_complex C) ⟶
  (alternating_face_map_complex C)) :=
{ app := λ _, Hσ q,
  naturality' := λ X Y f,
  begin
    unfold Hσ,
    rw [homotopy.comp_null_homotopic_map, homotopy.null_homotopic_map_comp],
    congr,
    rw [homotopy.comp_prehomotopy, homotopy.prehomotopy_comp],
    simp only [hσ'_naturality, chain_complex.of_hom_f,
      alternating_face_map_complex_map, alternating_face_map_complex.map],
  end }

/-- For each q, P q is a natural transformation. -/
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
      congr' 1,
      rw [← assoc, hq, assoc],
      congr' 1,
      exact (nat_trans_Hσ q).naturality' f, }
  end }

lemma P_termwise_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
   f.app (op [n]) ≫ (P q).f n = (P q).f n ≫ f.app (op [n]) :=
homological_complex.congr_hom ((nat_trans_P q).naturality f) n

/-- Q q is the complement projector associated to P q -/
def Q {X : simplicial_object C} (q : ℕ) : ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X) := 𝟙 _ - P q

/-- This is the decreasing involution of `fin (n+1)` which appears in `decomposition_Q`. -/
def reverse_fin {n : ℕ} (i : fin(n+1)) : fin(n+1):= ⟨n-i, nat.sub_lt_succ n ↑i⟩

lemma reverse_fin_eq {n a : ℕ} (i : fin(n+1)) (hnaq : n=a+i) : reverse_fin i = 
  ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
begin
  ext,
  simp only [reverse_fin, fin.coe_mk],
  exact tsub_eq_of_eq_add hnaq,
end

/-- We decompose the identity using `P_q` and degeneracies. In the case of a simplicial
abelian group, this means we can decompose a $(n+1)$-simplex $x$ as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is in the image of `P_q$ and
the $y_i$ are in degree $n$. -/
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

/-- The structure `morph_components` is an ad hoc structure that is used the 
proof of `normalized_Moore_complex_reflects_iso`. The fields are the data
that are needed in order to construct a morphism `X _[n+1] ⟶ Z` (see `F`)
using the decomposition of the identity given by `decomposition_Q n (n+1)`.

In the proof of `normalized_Moore_complex_reflects_iso`, in order to check
that two maps coincide, we only need to verify that the `morph_components`
they come from are equal.
-/
@[ext, nolint has_inhabited_instance]
structure morph_components (X : simplicial_object C) (n : ℕ) (Z : C) :=
  (a : X _[n+1] ⟶ Z) (b : fin(n+1) → (X _[n] ⟶ Z))

/-- The morphism `X _[n+1] ⟶ Z ` associated to a `morph_components X n Z`-/
def F {Z : C} {n : ℕ} {X : simplicial_object C} (f : morph_components X n Z) :
  X _[n+1] ⟶ Z :=
  P_infty.f (n+1) ≫ f.a + ∑ (i : fin (n+1)),
  (((P i).f (n+1)) ≫ (X.δ (reverse_fin i).succ) ≫ (f.b (reverse_fin i))) 

/-- the canonical `morph_components` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
def morph_components_id (X : simplicial_object C) (n : ℕ) :
  morph_components X n (X _[n+1]) :=
{ a := P_infty.f (n+1),
  b := λ i, X.σ i, }

lemma F_id (X : simplicial_object C) (n : ℕ) :
  F (morph_components_id X n) = 𝟙 _ :=
begin
  simp only [morph_components_id, F, P_infty_termwise,
    ← homological_complex.comp_f, P_is_a_projector (n+1),
    (show 𝟙 (X.obj (op [n+1])) = (P (n+1)).f (n+1)+(Q (n+1)).f (n+1), by
  { simp only [Q, homological_complex.sub_f_apply, add_sub_cancel'_right,
    homological_complex.id_f], refl, })],
  congr,
  rw decomposition_Q n (n+1) rfl.ge,
  congr,
  ext,
  simp only [true_and, true_iff, finset.mem_univ, finset.mem_filter, fin.is_lt],
end

/-- A `morph_components` can be postcomposed with a map `Z ⟶ Z'`. -/
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

/-- A `morph_components` can be precomposed with a map `X' ⟶ X`. -/
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

lemma N'_reflects_iso' {X Y : simplicial_object C}
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
    /- we have to construct an inverse to f in degree n, by induction on n -/
    induction n with n hn,
    /- degree 0 -/
    { use g.f 0,
      split,
      have eq := homological_complex.congr_hom hgf 0, swap,
      have eq := homological_complex.congr_hom hfg 0,
      all_goals {
        simpa only [homological_complex.comp_f, chain_complex.of_hom_f,
          alternating_face_map_complex.map, P_infty_termwise,
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
        { have eq := homological_complex.congr_hom hgf (n+1),
          simp only [homological_complex.comp_f, chain_complex.of_hom_f,
          alternating_face_map_complex.map, P_infty_termwise] at eq ⊢,
          rw [← assoc] at eq ⊢,
          simpa only [← P_termwise_naturality] using eq, },
        { simp only [is_iso.hom_inv_id_assoc], }, },
      { rw [← F_comp, ← F_id],
        congr,
        dsimp [morph_components_comp, morph_components_id],
        ext,
        { have eq := homological_complex.congr_hom hfg (n+1),
          simpa only [homological_complex.comp_f, chain_complex.of_hom_f,
          alternating_face_map_complex.map, P_infty_termwise, assoc] using eq, },
        { simp only [assoc],
          erw f.naturality,
          simpa only [is_iso.inv_hom_id_assoc], }, }, },
  end

namespace N'

abbreviation obj' (X : simplicial_object C) : karoubi (chain_complex C ℕ) :=
  ⟨(alternating_face_map_complex C).obj X, P_infty, P_infty_is_a_projector⟩

abbreviation map' {X Y : simplicial_object C} (f : X ⟶ Y) : obj' X ⟶ obj' Y :=
  ⟨P_infty ≫ (alternating_face_map_complex C).map f,
begin
  ext n,
  dsimp [P_infty],
  conv { to_lhs, congr, rw [← P_is_a_projector, homological_complex.comp_f], },
  slice_lhs 2 3 { rw ← P_termwise_naturality, },
  slice_rhs 1 2 { rw [← homological_complex.comp_f,
    P_is_a_projector], },
  rw assoc,
end⟩

end N'

@[simps]
def N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ) :=
{ obj := N'.obj',
  map := λ X Y f, N'.map' f,
  map_id' := λ X, begin
    ext n,
    simp only [homological_complex.comp_f, chain_complex.of_hom_f,
      nat_trans.id_app, alternating_face_map_complex_map,
      alternating_face_map_complex.map, karoubi.id_eq],
    erw comp_id,
  end,
  map_comp' := λ X Y Z f g, begin
    ext n,
    simp only [homological_complex.comp_f, karoubi.comp,
      alternating_face_map_complex.map, alternating_face_map_complex_map,
      chain_complex.of_hom_f, nat_trans.comp_app, P_infty],
      slice_rhs 2 3 { erw P_termwise_naturality, },
      slice_rhs 1 2 { rw [← homological_complex.comp_f,
        P_is_a_projector], },
      rw assoc,
  end }

theorem N'_reflects_iso : reflects_isomorphisms
  (N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
begin
  refine ⟨_⟩,
  intros X Y f,
  introI,
  let iso := as_iso (N'.map f),
  apply N'_reflects_iso' f iso.inv.1,
  { have h := iso.hom_inv_id,
    simpa only [karoubi.hom_ext, karoubi.comp, as_iso_hom,
      N'_map, assoc] using h, },
  { have h := iso.inv_hom_id,
    simp only [karoubi.hom_ext, karoubi.comp, as_iso_hom,
      N'_map] at h,
    conv at h { to_lhs, rw ← assoc, congr, erw karoubi.comp_p iso.inv, },
    erw [h, P_infty_is_a_projector], }
end

@[simp]
def N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) :=
  karoubi.functor_extension' N'

theorem N_reflects_iso : reflects_isomorphisms
  (N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)) :=
begin
  /- restating the result in a way that allows induction on the degree n -/
  refine ⟨_⟩,
  intros X Y f hf,
  haveI : is_iso ((karoubi_simplicial_object C).map f), swap,
  { exact is_iso_of_reflects_iso f (karoubi_simplicial_object C), },
  haveI : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (((karoubi_simplicial_object C).map f).app Δ), swap,
  { apply nat_iso.is_iso_of_is_iso_app, },
  intro s,
  let m := simplex_category.len (unop s),
  rw [show s = op [m], by { simp only [op_unop, simplex_category.mk_len], }],
  simp only [karoubi_simplicial_object_functor.map, karoubi_simplicial_object_map],
  generalize : m = n,
  /- restating the assumptions in a more practical form -/
  have p_comp_f := congr_app (karoubi.p_comp f),
  have comp_p_f := congr_app (karoubi.comp_p f),
  rcases f with ⟨f', comm_f⟩,
  rcases hf with ⟨⟨g, ⟨hgf, hfg⟩⟩⟩,
  have hgf' := homological_complex.congr_hom (karoubi.hom_ext.mp hgf),
  have hfg' := homological_complex.congr_hom (karoubi.hom_ext.mp hfg),
  have hg   := homological_complex.congr_hom g.comm,
  simp only [homological_complex.comp_f, karoubi.id_eq, karoubi.comp] at hgf' hfg' hg,
  dsimp at hgf' hfg' p_comp_f comp_p_f hg ⊢,
  clear hgf hfg m s,
  --have hg := g.idempotence,
  /- we have to construct an inverse to f in degree n, by induction on n -/
  induction n with n hn,
  /- degree 0 -/
  { use g.f.f 0; dsimp,
    { have eq := hg 0,
      simp only [P_infty_termwise, P_deg0_eq] at eq,
      erw [id_comp, id_comp] at eq,
      exact eq, },
    { split; ext; simp only [karoubi.id_eq, karoubi.comp,
        karoubi_simplicial_object_functor.obj_obj_p],
      have eq := hgf' 0, swap,
      have eq := hfg' 0,
      all_goals
      { simp only [P_infty_termwise, P_deg0_eq] at eq,
        erw [id_comp, id_comp] at eq,
        exact eq, }, }, },
  /- isomorphism in degree n+1 of an isomorphism in degree n -/
  { sorry, }
end

end dold_kan

end algebraic_topology
