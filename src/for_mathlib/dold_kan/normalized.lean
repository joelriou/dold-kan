/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.functor_n

/-

# Comparison with the normalized Moore complex functor

In this file, we show that when the category `A` is abelian,
there is an isomorphism `N₁_iso_to_karoubi_normalized A` between
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)`
defined in `functor_n.lean` and the composition of
`normalized_Moore_complex A` with the inclusion
`chain_complex A ℕ ⥤ karoubi (chain_complex A ℕ)`.

This isomorphism shall be used in `equivalence.lean` in order to obtain
the Dold-Kan equivalence
`category_theory.abelian.dold_kan.equivalence : simplicial_object A ≌ chain_complex A ℕ`
with a functor (definitionally) equal to `normalized_Moore_complex A`.

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.subobject
open category_theory.idempotents
open_locale dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {A : Type*} [category A] [abelian A]
variables {X : simplicial_object A}

lemma higher_faces_vanish_on_Moore_complex (n : ℕ) :
  higher_faces_vanish (n+1) ((inclusion_of_Moore_complex_map X).f (n+1)) := λ j hj,
begin
  simp only [inclusion_of_Moore_complex_map, chain_complex.of_hom],
  erw ← factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ
    _ j (by simp only [finset.mem_univ])),
  slice_lhs 2 3 { rw kernel_subobject_arrow_comp, },
  rwa [comp_zero],
end

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

lemma P_infty_factors_thru_Moore_complex_degreewise (n : ℕ) :
  subobject.factors (normalized_Moore_complex.obj_X X n) (P_infty.f n) :=
begin
  rw [P_infty_degreewise],
  cases n; rw [normalized_Moore_complex.obj_X],
  { apply top_factors, },
  { rw finset_inf_factors,
    intros i hi,
    apply kernel_subobject_factors,
    exact (higher_faces_vanish_P (n+1) n) i (le_add_self), }
end

/-- P_infty factors through the normalized_Moore_complex -/
@[simps]
def P_infty_into_Moore_subcomplex (X : simplicial_object A) : K[X] ⟶ N[X] :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, factor_thru _ _ (P_infty_factors_thru_Moore_complex_degreewise n))
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
  exact P_infty_degreewise_is_a_projection n,
end

lemma P_infty_comp_P_infty_into_Moore_subcomplex (X : simplicial_object A) :
P_infty ≫ P_infty_into_Moore_subcomplex X = P_infty_into_Moore_subcomplex X :=
begin
  ext1, ext1 n,
  simp only [homological_complex.comp_f],
  exact P_infty_comp_P_infty_into_Moore_subcomplex_degreewise X n,
end

lemma P_infty_into_Moore_subcomplex_degreewise_naturality {X Y : simplicial_object A} (f : X ⟶ Y) (n : ℕ) :
(alternating_face_map_complex.map f).f n ≫ (P_infty_into_Moore_subcomplex Y).f n =
(P_infty_into_Moore_subcomplex X).f n ≫ ((normalized_Moore_complex A).map f).f n :=
begin
  ext1 n,
  dsimp [P_infty_into_Moore_subcomplex],
  simp only [assoc, factor_thru_arrow, factor_thru_arrow_assoc],
  apply P_infty_degreewise_naturality,
end

lemma P_infty_into_Moore_subcomplex_naturality {X Y : simplicial_object A} (f : X ⟶ Y) :
alternating_face_map_complex.map f ≫ P_infty_into_Moore_subcomplex Y =
P_infty_into_Moore_subcomplex X ≫ normalized_Moore_complex.map f :=
begin
  ext1, ext1 n,
  simp only [homological_complex.comp_f],
  exact P_infty_into_Moore_subcomplex_degreewise_naturality f n,
end

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

lemma P_infty_is_a_retraction (Y : simplicial_object A) :
  inclusion_of_Moore_complex_map Y ≫ P_infty_into_Moore_subcomplex Y = 𝟙 _ :=
begin
  ext n,
  erw [assoc, factor_thru_arrow, id_comp, inclusion_of_Moore_complex_comp_P_infty_degreewise],
  refl,
end

lemma factors_P_infty (Y : simplicial_object A) :
  P_infty_into_Moore_subcomplex Y ≫ inclusion_of_Moore_complex_map Y = P_infty :=
begin
  ext n,
  simp only [P_infty_into_Moore_subcomplex, chain_complex.of_hom,
    factor_thru_arrow, homological_complex.comp_f, inclusion_of_Moore_complex_map_f],
end

variable (A)

/-- When the category `A` is abelian,
the functor `N₁ : simplicial_object A ⥤ karoubi (chain_complex A ℕ)` defined
using `P_infty` identifies to the composition of normalized Moore complex functor
and the inclusion in the Karoubi envelope. -/
def N₁_iso_to_karoubi_normalized :
  N₁ ≅ (normalized_Moore_complex A ⋙ to_karoubi _) :=
{ hom :=
  { app := λ X,
    { f := P_infty_into_Moore_subcomplex X,
      comm := by erw [comp_id, P_infty_comp_P_infty_into_Moore_subcomplex X] },
    naturality' := λ X Y f, begin
      ext1,
      simp only [karoubi.comp, N₁_map_f, assoc],
      erw [P_infty_into_Moore_subcomplex_naturality, ← assoc,
        P_infty_comp_P_infty_into_Moore_subcomplex],
      refl,
    end },
  inv :=
  { app := λ X,
    { f := (inclusion_of_Moore_complex A).app X,
      comm := by erw [id_comp, inclusion_of_Moore_complex_comp_P_infty], },
    naturality' := λ X Y f, begin
      ext1,
      simp only [karoubi.comp],
      erw [(inclusion_of_Moore_complex A).naturality f, ← assoc,
        inclusion_of_Moore_complex_comp_P_infty X],
      refl,
    end },
  hom_inv_id' := begin
    ext X n,
    simpa only [inclusion_of_Moore_complex_app, nat_trans.comp_app, karoubi.comp,
      homological_complex.comp_f, P_infty_into_Moore_subcomplex_f,
      inclusion_of_Moore_complex_map_f, factor_thru_arrow],
  end,
  inv_hom_id' := begin
    ext X n,
    simp only [karoubi.comp, assoc, inclusion_of_Moore_complex_app, nat_trans.comp_app,
      homological_complex.comp_f, inclusion_of_Moore_complex_map_f,
      P_infty_into_Moore_subcomplex_f, factor_thru_arrow, nat_trans.id_app, karoubi.id_eq],
    erw [inclusion_of_Moore_complex_comp_P_infty_degreewise, id_comp],
    refl,
  end }

end dold_kan

end algebraic_topology
