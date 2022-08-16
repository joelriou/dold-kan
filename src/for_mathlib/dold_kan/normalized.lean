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

section
variables {C : Type*} [category C] [abelian C]

@[simp]
lemma normalized_Moore_complex_obj_d (X : simplicial_object C) (n : ℕ) :
  ((normalized_Moore_complex C).obj X).d (n+1) n =
  normalized_Moore_complex.obj_d X n :=
by apply chain_complex.of_d

end

namespace dold_kan

universe v

variables {A : Type*} [category A] [abelian A]
variables {X : simplicial_object A}

lemma higher_faces_vanish.on_Moore_complex (n : ℕ) :
  higher_faces_vanish (n+1) ((inclusion_of_Moore_complex_map X).f (n+1)) := λ j hj,
begin
  dsimp [inclusion_of_Moore_complex_map],
  rw [← factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ
    _ j (by simp only [finset.mem_univ])), assoc, kernel_subobject_arrow_comp, comp_zero],
end

lemma P_infty_factors_thru_Moore_complex_degreewise (n : ℕ) :
  subobject.factors (normalized_Moore_complex.obj_X X n) (P_infty.f n) :=
begin
  cases n,
  { apply top_factors, },
  { rw [P_infty_f, normalized_Moore_complex.obj_X, finset_inf_factors],
    intros i hi,
    apply kernel_subobject_factors,
    exact (higher_faces_vanish.of_P (n+1) n) i (le_add_self), }
end

/-- P_infty factors through the normalized_Moore_complex -/
@[simps]
def P_infty_into_Moore_subcomplex (X : simplicial_object A) : K[X] ⟶ N[X] :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, factor_thru _ _ (P_infty_factors_thru_Moore_complex_degreewise n))
  (λ n, begin
    rw [← cancel_mono (normalized_Moore_complex.obj_X X n).arrow, assoc, assoc,
      factor_thru_arrow, ← inclusion_of_Moore_complex_map_f,
      ← normalized_Moore_complex_obj_d, ← (inclusion_of_Moore_complex_map X).comm' (n+1) n rfl,
      inclusion_of_Moore_complex_map_f, factor_thru_arrow_assoc,
      ← alternating_face_map_complex_obj_d],
    exact P_infty.comm' (n+1) n rfl,
    end)

@[simp, reassoc]
lemma P_infty_into_Moore_subcomplex_comp_inclusion (X : simplicial_object A) :
  P_infty_into_Moore_subcomplex X ≫ inclusion_of_Moore_complex_map X = P_infty := by tidy

@[simp, reassoc]
lemma P_infty_into_Moore_subcomplex_naturality {X Y : simplicial_object A} (f : X ⟶ Y) :
  alternating_face_map_complex.map f ≫ P_infty_into_Moore_subcomplex Y =
    P_infty_into_Moore_subcomplex X ≫ normalized_Moore_complex.map f := by tidy

@[simp, reassoc]
lemma P_infty_comp_P_infty_into_Moore_subcomplex (X : simplicial_object A) :
  P_infty ≫ P_infty_into_Moore_subcomplex X = P_infty_into_Moore_subcomplex X := by tidy

@[simp, reassoc]
lemma inclusion_of_Moore_complex_map_comp_P_infty (X : simplicial_object A) :
  inclusion_of_Moore_complex_map X ≫ P_infty = inclusion_of_Moore_complex_map X :=
begin
  ext n,
  cases n,
  { dsimp, simp only [comp_id], },
  { exact (higher_faces_vanish.on_Moore_complex n).comp_P_eq_self, },
end

instance : mono (inclusion_of_Moore_complex_map X) :=
⟨λ Y f₁ f₂ hf, by { ext n, exact homological_complex.congr_hom hf n, }⟩

/-- `inclusion_of_Moore_complex_map X` is a split mono. -/
def split_mono_inclusion_of_Moore_complex_map (X : simplicial_object A) :
  split_mono (inclusion_of_Moore_complex_map X) :=
{ retraction := P_infty_into_Moore_subcomplex X,
  id' := by simp only [← cancel_mono (inclusion_of_Moore_complex_map X), assoc, id_comp,
    P_infty_into_Moore_subcomplex_comp_inclusion, inclusion_of_Moore_complex_map_comp_P_infty], }

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
      comm := by tidy, }, },
  inv :=
  { app := λ X,
    { f := inclusion_of_Moore_complex_map X,
      comm := by tidy, }, },
  hom_inv_id' := begin
    ext X : 3,
    simp only [P_infty_into_Moore_subcomplex_comp_inclusion, nat_trans.comp_app,
      karoubi.comp, N₁_obj_p, nat_trans.id_app, karoubi.id_eq],
  end,
  inv_hom_id' := begin
    ext X : 3,
    simp only [← cancel_mono (inclusion_of_Moore_complex_map X),
      nat_trans.comp_app, karoubi.comp, assoc, P_infty_into_Moore_subcomplex_comp_inclusion,
      inclusion_of_Moore_complex_map_comp_P_infty, nat_trans.id_app, karoubi.id_eq],
    dsimp only [functor.comp_obj, to_karoubi],
    rw id_comp,
  end }

end dold_kan

end algebraic_topology
