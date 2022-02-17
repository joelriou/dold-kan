/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functor_n
--import for_mathlib.idempotents.functor_categories
--import for_mathlib.idempotents.functor_extension

open category_theory
open category_theory.category
open category_theory.limits
--open category_theory.preadditive
open category_theory.subobject
--open category_theory.simplicial_object
open category_theory.idempotents
--open simplex_category
--open opposite
--open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {A : Type*} [category A] [abelian A]
variables {X : simplicial_object A}

lemma higher_faces_vanish_on_Moore_complex (n : ℕ) :
  higher_faces_vanish (n+1) ((inclusion_of_Moore_complex_map X).f (n+1)) :=
{ vanishing := λ j hj,
  begin
    simp only [inclusion_of_Moore_complex_map, chain_complex.of_hom],
    erw ← factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ
      _ j (by simp only [finset.mem_univ])),
    slice_lhs 2 3 { rw kernel_subobject_arrow_comp, },
    rwa [comp_zero],
  end }

lemma P_infty_on_Moore_complex :
inclusion_of_Moore_complex_map X ≫ P_infty = inclusion_of_Moore_complex_map X :=
begin
  ext n,
  simp only [homological_complex.comp_f],
  cases n,
  { erw [P_deg0_eq, comp_id], },
  { rw [P_infty_degreewise],
    exact P_is_identity_where_faces_vanish (higher_faces_vanish_on_Moore_complex n), },
end

lemma P_infty_factors_thru_Moore_complex_degree_wise (n : ℕ) :
  subobject.factors (normalized_Moore_complex.obj_X X n) (P_infty.f n) :=
begin
  rw [P_infty_degreewise],
  cases n; rw [normalized_Moore_complex.obj_X],
  { apply top_factors, },
  { rw finset_inf_factors _,
    intros i hi,
    apply kernel_subobject_factors,
    exact (higher_faces_vanish_P (n+1) n).vanishing i (le_add_self), }
end

/-- P_infty factors through the normalized_Moore_complex -/
@[simps]
def P_infty_into_Moore_subcomplex (X : simplicial_object A) :
  (alternating_face_map_complex A).obj X ⟶ (normalized_Moore_complex A).obj X :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, factor_thru _ _ (P_infty_factors_thru_Moore_complex_degree_wise n))
  (λ n,
    begin
      apply (cancel_mono (normalized_Moore_complex.obj_X X n).arrow).mp,
      simp only [assoc, factor_thru_arrow],
      have eq := (inclusion_of_Moore_complex_map X).comm' (n+1) n (by simp only [complex_shape.down_rel]),
      rw [(show (inclusion_of_Moore_complex_map X).f n = (normalized_Moore_complex.obj_X X n).arrow, by refl),
        (show ((normalized_Moore_complex A).obj X).d (n+1) n = normalized_Moore_complex.obj_d X n,
          by erw chain_complex.of_d)] at eq,
      erw [← eq, ← assoc, factor_thru_arrow,
        P_infty.comm' (n+1) n (by simp only [complex_shape.down_rel]), chain_complex.of_d],
    end)
  
lemma P_infty_comp_P_infty_into_Moore_subcomplex_degreewise (X : simplicial_object A) (n : ℕ) :
P_infty.f n ≫ (P_infty_into_Moore_subcomplex X).f n = (P_infty_into_Moore_subcomplex X).f n :=
begin
  ext,
  rw [assoc],
  dsimp [P_infty_into_Moore_subcomplex],
  simp only [factor_thru_arrow],
  exact P_infty_degreewise_is_a_projector n,
end

lemma P_infty_comp_P_infty_into_Moore_subcomplex (X : simplicial_object A) :
P_infty ≫ P_infty_into_Moore_subcomplex X = P_infty_into_Moore_subcomplex X :=
begin
  ext1, ext1 n,
  simp only [homological_complex.comp_f],
  exact P_infty_comp_P_infty_into_Moore_subcomplex_degreewise X n,
end

lemma P_infty_into_Moore_subcomplex_degreewise_naturality {X Y : simplicial_object A} (f : X ⟶ Y) (n : ℕ) :
((alternating_face_map_complex A).map f).f n ≫ (P_infty_into_Moore_subcomplex Y).f n =
(P_infty_into_Moore_subcomplex X).f n ≫ ((normalized_Moore_complex A).map f).f n :=
begin
  ext1 n,
  dsimp [P_infty_into_Moore_subcomplex],
  simp only [assoc, factor_thru_arrow, factor_thru_arrow_assoc],
  apply P_infty_degreewise_naturality,
end

lemma P_infty_into_Moore_subcomplex_naturality {X Y : simplicial_object A} (f : X ⟶ Y) :
((alternating_face_map_complex A).map f) ≫ (P_infty_into_Moore_subcomplex Y) =
P_infty_into_Moore_subcomplex X ≫ (normalized_Moore_complex A).map f :=
begin
  ext1, ext1 n,
  simp only [homological_complex.comp_f],
  exact P_infty_into_Moore_subcomplex_degreewise_naturality f n,
end

@[simps]
def N'_to_karoubi_normalized :
  N' ⟶ (normalized_Moore_complex A ⋙ to_karoubi _) :=
{ app := λ X,
  { f := P_infty_into_Moore_subcomplex X,
    comm := by erw [comp_id, P_infty_comp_P_infty_into_Moore_subcomplex X] },
  naturality' := λ X Y f, begin
    ext1,
    simp only [karoubi.comp, N'_map, N'_functor.map_f, assoc,
      P_infty_into_Moore_subcomplex_naturality],
    simpa only [← assoc, P_infty_comp_P_infty_into_Moore_subcomplex],
  end }

lemma inclusion_of_Moore_complex_comp_P_infty (X : simplicial_object A) :
(inclusion_of_Moore_complex A).app X ≫ P_infty = (inclusion_of_Moore_complex A).app X :=
begin
  ext1, ext1 n,
  simp only [homological_complex.comp_f],
  cases n,
  { erw comp_id, },
  { exact P_is_identity_where_faces_vanish (higher_faces_vanish_on_Moore_complex n), },
end

lemma inclusion_of_Moore_complex_comp_P_infty_degreewise (X : simplicial_object A) (n : ℕ):
((inclusion_of_Moore_complex A).app X).f n ≫ P_infty.f n = ((inclusion_of_Moore_complex A).app X).f n :=
homological_complex.congr_hom (inclusion_of_Moore_complex_comp_P_infty X) n

@[simps]
def to_karoubi_normalized_to_N' :
  (normalized_Moore_complex A ⋙ to_karoubi _) ⟶ N' :=
{ app := λ X,
  { f := (inclusion_of_Moore_complex A).app X,
    comm := by erw [id_comp, inclusion_of_Moore_complex_comp_P_infty], },
  naturality' := λ X Y f, begin
    ext1,
    simp only [karoubi.comp],
    erw [(inclusion_of_Moore_complex A).naturality f, ← assoc, inclusion_of_Moore_complex_comp_P_infty X],
  end }

variable (A)

def N'_equiv_karoubi_normalized :
  N' ≅ (normalized_Moore_complex A ⋙ to_karoubi _) :=
{ hom := N'_to_karoubi_normalized,
  inv := to_karoubi_normalized_to_N',
  hom_inv_id' := begin
    ext X n,
    simpa only [N'_to_karoubi_normalized_app_f, to_karoubi_normalized_to_N'_app_f,
      inclusion_of_Moore_complex_app, nat_trans.comp_app, karoubi.comp, homological_complex.comp_f,
      P_infty_into_Moore_subcomplex_f, inclusion_of_Moore_complex_map_f, factor_thru_arrow],
  end,
  inv_hom_id' := begin
    ext X n,
    simp only [to_karoubi_normalized_to_N'_app_f, inclusion_of_Moore_complex_app,
      N'_to_karoubi_normalized_app_f, nat_trans.comp_app, karoubi.comp,
        homological_complex.comp_f, inclusion_of_Moore_complex_map_f,
        P_infty_into_Moore_subcomplex_f, assoc, factor_thru_arrow, nat_trans.id_app, karoubi.id_eq],
    erw [inclusion_of_Moore_complex_comp_P_infty_degreewise, id_comp],
    refl,
  end }

end dold_kan

end algebraic_topology
