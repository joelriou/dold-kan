/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.projections
import for_mathlib.idempotents.functor_categories
import for_mathlib.idempotents.functor_extension

/-

# Construction of the projection `P_infty` for the Dold-Kan correspondence

In this file, we construct the projection `P_infty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `P_infty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.
(See `equivalence.lean` for the general strategy of proof.)

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.idempotents
open simplex_category
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {C : Type*} [category.{v} C] [preadditive C]
variables {X : simplicial_object C}

lemma P_is_eventually_constant {q n : ℕ} (hqn : n≤q) :
  ((P (q+1)).f n : X _[n] ⟶ _ ) = (P q).f n :=
begin
  cases n,
  { simp only [P_deg0_eq], },
  { unfold P,
    simp only [add_right_eq_self, comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id],
    exact Hσφ_eq_zero (nat.succ_le_iff.mp hqn) (higher_faces_vanish_P q n), }
end

/-- Definition of P_infty from the P q -/
def P_infty : K[X] ⟶ K[X] := chain_complex.of_hom _ _ _ _ _ _
    (λ n, ((P n).f n : X _[n] ⟶ _ ))
begin
  intro n,
  simp only [← P_is_eventually_constant (rfl.ge : n≤n)],
  have eq := (P (n+1) : K[X] ⟶ _).comm (n+1) n,
  erw chain_complex.of_d at eq,
  exact eq,
end

lemma P_infty_degreewise (n : ℕ) :
  (P_infty.f n : X _[n] ⟶  X _[n] ) = (P n).f n := by refl

lemma P_infty_degreewise_is_a_projection (n : ℕ) :
  (P_infty.f n : X _[n] ⟶ _) ≫ (P_infty.f n) = P_infty.f n :=
by simp only [P_infty_degreewise, P_degreewise_is_a_projection]

lemma P_infty_is_a_projection : (P_infty : K[X] ⟶ _) ≫ P_infty = P_infty :=
by { ext n, exact P_infty_degreewise_is_a_projection n, }

lemma P_infty_degreewise_naturality (n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ P_infty.f n = P_infty.f n ≫ f.app (op [n]) :=
P_degreewise_naturality n n f

variable (C)

/-- `P_infty` induces a natural transformation, i.e. an endomorphism of
the functor `alternating_face_map_complex C`. -/
@[simps]
def nat_trans_P_infty :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ _, P_infty,
  naturality' := λ X Y f, by { ext n, exact P_infty_degreewise_naturality n f, }, }

/-- The natural transformation in each degree that is induced by `nat_trans_P_infty`. -/
@[simps]
def nat_trans_P_infty_degreewise (n : ℕ) :=
nat_trans_P_infty C ◫ 𝟙 (homological_complex.eval _ _ n)

variable {C}

@[simp]
lemma map_P_infty_degreewise {D : Type*} [category.{v} D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (n : ℕ) :
  (P_infty : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
  G.map ((P_infty : alternating_face_map_complex.obj X ⟶ _).f n) :=
by simp only [P_infty_degreewise, map_P]

/-- Given an object `Y : karoubi (simplicial_object C)`, this lemma
computes `P_infty` for the associated object in `simplicial_object (karoubi C)`
in terms of `P_infty` for `Y.X : simplicial_object C` and `Y.p`. -/
lemma karoubi_P_infty_f {Y : karoubi (simplicial_object C)} (n : ℕ) :
  ((P_infty : K[(karoubi_functor_category_embedding _ _).obj Y] ⟶ _).f n).f =
  Y.p.app (op [n]) ≫ (P_infty : K[Y.X] ⟶ _).f n :=
begin
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubi_functor_category_embedding _ _).obj Y,
  let Y₂ := Y.X,
  let Y₃ := (((whiskering _ _).obj (to_karoubi C)).obj Y.X),
  let Y₄ := (karoubi_functor_category_embedding _ _).obj ((to_karoubi _).obj Y.X),
  let P₁ : K[Y₁] ⟶ _ := P_infty,
  let P₂ : K[Y₂] ⟶ _ := P_infty,
  let P₃ : K[Y₃] ⟶ _ := P_infty,
  let P₄ : K[Y₄] ⟶ _ := P_infty,
  -- The statement of lemma relates P₁ and P₂.
  suffices h₁₂ : (P₁.f n).f = Y.p.app (op [n]) ≫ P₂.f n,
  { exact h₁₂, },
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n :=
    karoubi.hom_ext.mp (map_P_infty_degreewise (to_karoubi C) Y₂ n),
  have h₄₃ : P₄.f n = P₃.f n,
  { have eq := nat_trans_P_infty_degreewise_app (karoubi C) n,
    erw [← eq Y₃, ← eq Y₄],
    congr,
    exact congr_obj (to_karoubi_comp_karoubi_functor_category_embedding _ _) Y₂, },
  let τ₁ := 𝟙 (karoubi_functor_category_embedding (simplex_categoryᵒᵖ) C),
  let τ₂ := nat_trans_P_infty_degreewise (karoubi C) n,
  let τ := τ₁ ◫ τ₂,
  have h₁₄ := idempotents.nat_trans_eq' τ Y,
  dsimp [τ, τ₁, τ₂, nat_trans_P_infty_degreewise] at h₁₄,
  erw [id_comp, id_comp, comp_id, comp_id] at h₁₄,
  erw [h₁₄, ← h₃₂, ← h₄₃],
  simp only [karoubi_functor_category_embedding.map_app_f, karoubi.decomp_id_p_f,
    karoubi.decomp_id_i_f, karoubi.comp],
  let π : Y₄ ⟶ Y₄ := (to_karoubi _ ⋙ karoubi_functor_category_embedding _ _).map Y.p,
  have eq := karoubi.hom_ext.mp (P_infty_degreewise_naturality n π),
  simp only [karoubi.comp] at eq,
  erw [← eq, ← assoc],
  congr,
  exact congr_app Y.idem (op [n]),
end

end dold_kan

end algebraic_topology
