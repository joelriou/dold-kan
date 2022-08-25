/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.degeneracies
import for_mathlib.dold_kan.normalized
import tactic.fin_cases

noncomputable theory

namespace category_theory

open limits preadditive

variables {C : Type*} [category C]

lemma subobject.le_iff {X : C} (A B : subobject X) :
  A ≤ B ↔ B.factors A.arrow :=
begin
  split,
  { intro h,
    rw subobject.factors_iff,
    exact ⟨subobject.of_le _ _ h,
      by simp only [subobject.representative_arrow, subobject.of_le_arrow]⟩, },
  { intro h,
    exact subobject.le_of_comm (B.factor_thru _ h) (subobject.factor_thru_arrow _ _ _), }
end

section
variables [abelian C] {I : Type*} [fintype I] {B : C} (P : I → subobject B)
@[simp]
def coproduct_to_finset_univ_sup : ∐ (λ (i : I), (P i : C)) ⟶ ↑(finset.univ.sup P) :=
sigma.desc (λ i, subobject.of_le _ _ (finset.le_sup (finset.mem_univ _)))

lemma subobject.jointly_epi_to_binary_sup {B : C} (P₁ P₂ : subobject B) {Z : C}
  (f₁ f₂ : ↑(P₁ ⊔ P₂) ⟶ Z)
  (hl : subobject.of_le P₁ (P₁ ⊔ P₂) le_sup_left ≫ f₁ =
    subobject.of_le P₁ (P₁ ⊔ P₂) le_sup_left ≫ f₂)
  (hr : subobject.of_le P₂ (P₁ ⊔ P₂) le_sup_right ≫ f₁ =
    subobject.of_le P₂ (P₁ ⊔ P₂) le_sup_right ≫ f₂) : f₁ = f₂ :=
begin
  revert P₁ P₂,
  refine subobject.ind₂ _ _,
  introsI A₁ A₂ f₁ f₂ hf₁ hf₂ g₁ g₂ h₁ h₂,
  let f₁₂ := (mono_over.sup.obj (mono_over.mk' f₁)).obj (mono_over.mk' f₂),
  have eq : subobject.mk f₁ ⊔ subobject.mk f₂ = (to_thin_skeleton _).obj f₁₂ := rfl,
  let e := subobject.iso_of_eq (subobject.mk f₁ ⊔ subobject.mk f₂)
    ((to_thin_skeleton _).obj f₁₂) rfl,
  rw ← cancel_epi e.inv,
  all_goals { sorry, },
end

lemma subobject.jointly_epi_to_sup {I : Type*} (s : finset I) {B : C}
  (P : I → subobject B) {Z : C} (f₁ f₂ : ↑(s.sup P) ⟶ Z)
  (h : ∀ (i : s), subobject.of_le (P i) _ (finset.le_sup i.2)  ≫ f₁ =
    subobject.of_le (P i) _ (finset.le_sup i.2)  ≫ f₂) :
     f₁ = f₂ :=
begin
  revert f₁ f₂ h,
  induction s using finset.cons_induction_on with j s hj hs,
  { intros f₁ f₂ h,
    apply is_initial.hom_ext,
    simpa only [finset.sup_empty] using
      is_initial.of_iso initial_is_initial subobject.bot_coe_iso_initial.symm, },
  { intros f₁ f₂ h,
    let e := subobject.iso_of_eq ((finset.cons j s hj).sup P) (P j ⊔ s.sup P)
      (finset.sup_cons _),
    rw ← cancel_epi e.inv,
    apply subobject.jointly_epi_to_binary_sup,
    { simpa only [subobject.iso_of_eq_inv, subobject.of_le_comp_of_le_assoc]
        using h ⟨j, finset.mem_cons_self j s⟩, },
    { apply hs,
      intro i,
      simpa only [subobject.iso_of_eq_inv, subobject.of_le_comp_of_le_assoc]
        using h ⟨i.1 , finset.mem_cons.2 (or.inr i.2)⟩, }, },
end

lemma subobject.jointly_epi_to_univ_sup {I : Type*} [fintype I] {B : C}
  (P : I → subobject B) {Z : C} (f₁ f₂ : ↑(finset.univ.sup P) ⟶ Z)
  (h : ∀ (i : I), subobject.of_le (P i) _ (finset.le_sup (finset.mem_univ _)) ≫ f₁ =
    subobject.of_le (P i) _ (finset.le_sup (finset.mem_univ _)) ≫ f₂) : f₁ = f₂ :=
subobject.jointly_epi_to_sup _ _ _ _ (λ i, h i.1)

instance : epi (coproduct_to_finset_univ_sup P) :=
⟨λ Z f₁ f₂ h, subobject.jointly_epi_to_univ_sup _ _ _
  (λ i, by simpa only [coproduct_to_finset_univ_sup, colimit.ι_desc_assoc, cofan.mk_ι_app]
    using sigma.ι _ i ≫= h)⟩

lemma ι_comp_coproduct_to_finset_univ_sup_comp_arrow (i : I) :
  sigma.ι _ i ≫ coproduct_to_finset_univ_sup P ≫ (finset.univ.sup P).arrow = (P i).arrow :=
by simp only [coproduct_to_finset_univ_sup, colimit.ι_desc_assoc, cofan.mk_ι_app,
  subobject.of_le_arrow]

end

lemma subobject.factors_sum {X Y : C} [preadditive C] {P : subobject Y} {I : Type*}
  (s : finset I) (f : I → (X ⟶ Y)) (hf : ∀ (i : I) (hi : i ∈ s), P.factors (f i)) :
  P.factors (s.sum f) :=
begin
  rw subobject.factors_iff,
  refine ⟨finset.univ.sum (λ (j : s), P.factor_thru (f j) (hf j.1 j.2)), _⟩,
  simp only [subobject.representative_arrow, sum_comp,
    subobject.factor_thru_arrow, finset.sum_coe_sort],
end

end category_theory

open category_theory category_theory.limits opposite category_theory.preadditive
  category_theory.category algebraic_topology.dold_kan
open_locale simplicial dold_kan

namespace algebraic_topology

variables {C : Type*} [category C] [abelian C]

namespace degenerate_subcomplex

@[simp]
def obj_X (X : simplicial_object C) : Π (n : ℕ), subobject (K[X].X n)
| 0 := ⊥
| (n+1) := finset.univ.sup (λ (i : fin (n+1)), image_subobject (X.σ i))

lemma obj_X_factors_σ (X : simplicial_object C)
  {n : ℕ} (i : fin (n+1)) : (obj_X X (n+1)).factors (X.σ i) :=
subobject.finset_sup_factors ⟨i, finset.mem_univ _, ⟨factor_thru_image (X.σ i), by simp⟩⟩

lemma obj_X_factors_of_not_mono (X : simplicial_object C)
  (n : ℕ) {Δ : simplex_category} (θ : [n] ⟶ Δ) (hθ : ¬mono θ) :
  (obj_X X n).factors (X.map θ.op) :=
begin
  rw simplex_category.mono_iff_injective at hθ,
  cases n,
  { exfalso,
    apply hθ,
    intros x y h,
    fin_cases x,
    fin_cases y, },
  { rcases simplex_category.eq_σ_comp_of_not_injective θ hθ with ⟨i, α, h⟩,
    rw [h, op_comp, X.map_comp],
    apply subobject.factors_of_factors_right,
    apply obj_X_factors_σ, },
end

@[derive epi]
def coproduct_to_obj_X (X : simplicial_object C) (n : ℕ) :
  ∐ (λ (i : fin (n+1)), (image_subobject (X.σ i): C)) ⟶ ↑(obj_X X (n+1)) :=
coproduct_to_finset_univ_sup (λ (i : fin (n + 1)), image_subobject (X.σ i))

@[reassoc]
lemma ι_coproduct_to_obj_X_comp_arrow (X : simplicial_object C) {n : ℕ} (i : fin (n+1)) :
  sigma.ι _ i ≫ coproduct_to_obj_X X n ≫ (obj_X X (n+1)).arrow =
  (image_subobject (X.σ i)).arrow :=
by apply ι_comp_coproduct_to_finset_univ_sup_comp_arrow

@[simp, reassoc]
lemma obj_X_arrow_comp_P_infty (X : simplicial_object C) (n : ℕ) :
  (obj_X X n).arrow ≫ P_infty.f n = 0 :=
begin
  cases n,
  { dsimp [obj_X],
    simp only [subobject.bot_arrow, zero_comp], },
  { rw ← cancel_epi (coproduct_to_obj_X X n),
    ext,
    discrete_cases,
    simp only [ι_coproduct_to_obj_X_comp_arrow_assoc, comp_zero,
      ← cancel_epi (factor_thru_image_subobject (X.σ j)),
      image_subobject_arrow_comp_assoc, σ_comp_P_infty], },
end

@[simp, reassoc]
lemma obj_X_arrow_comp_Q_infty (X : simplicial_object C) (n : ℕ) :
  (obj_X X n).arrow ≫ Q_infty.f n = (obj_X X n).arrow :=
by simp only [Q_infty, homological_complex.sub_f_apply, homological_complex.id_f,
    comp_sub, comp_id, obj_X_arrow_comp_P_infty, sub_zero]

lemma obj_X_factors_Q (X : simplicial_object C) (n : ℕ) :
  (obj_X X n).factors (Q_infty.f n) :=
begin
  rw Q_infty_f,
  cases n,
  { simpa only [Q_f_0_eq, obj_X] using subobject.factors_zero, },
  { rw decomposition_Q n (n+1),
    apply subobject.factors_sum,
    intros i hi,
    apply subobject.factors_of_factors_right,
    apply subobject.factors_of_factors_right,
    apply obj_X_factors_σ, },
end

@[simp]
lemma obj_X_factors_iff_comp_P_infty_eq_zero (X : simplicial_object C) {Y : C} (n : ℕ)
  (f : Y ⟶ X _[n]) :
  (obj_X X n).factors f ↔ f ≫ P_infty.f n = 0 :=
begin
  split,
  { intro h,
    rw [← (obj_X X n).factor_thru_arrow _ h, assoc, obj_X_arrow_comp_P_infty, comp_zero], },
  { intro h,
    have h' : f ≫ Q_infty.f n = f,
    { rw P_infty_f at h,
      rw Q_infty_f,
      dsimp only [Q],
      simpa only [homological_complex.sub_f_apply, homological_complex.id_f, comp_sub,
        h, sub_zero] using comp_id f, },
    rw ← h',
    exact subobject.factors_of_factors_right _ (obj_X_factors_Q _ _), },
end

lemma obj_X_eq_kernel_P_infty (X : simplicial_object C) (n : ℕ) :
  obj_X X n = kernel_subobject (P_infty.f n) :=
begin
  apply le_antisymm; rw subobject.le_iff,
  { rw [kernel_subobject_factors_iff, ← obj_X_factors_iff_comp_P_infty_eq_zero],
    apply subobject.factors_self, },
  { rw [obj_X_factors_iff_comp_P_infty_eq_zero, kernel_subobject_arrow_comp], },
end

lemma d_factors_obj_X (X : simplicial_object C) (i j : ℕ) :
  (obj_X X j).factors ((obj_X X i).arrow ≫ K[X].d i j) :=
by rw [obj_X_factors_iff_comp_P_infty_eq_zero, assoc, ← P_infty.comm i j,
  obj_X_eq_kernel_P_infty, kernel_subobject_arrow_comp_assoc, zero_comp]

@[simps]
def obj (X : simplicial_object C) : chain_complex C ℕ :=
{ X := λ n, obj_X X n,
  d := λ i j, (obj_X X j).factor_thru _ (d_factors_obj_X X i j),
  shape' := λ i j hij, by { ext, rw [subobject.factor_thru_arrow,
    K[X].shape i j hij, zero_comp, comp_zero], },
  d_comp_d' := λ i j k hij hjk, by { ext, simp only [assoc, comp_zero, zero_comp,
    subobject.factor_thru_arrow, subobject.factor_thru_arrow_assoc, K[X].d_comp_d], }, }

lemma map_factors_obj_X {X Y : simplicial_object C} (f : X ⟶ Y) (n : ℕ) :
  (obj_X Y n).factors ((obj_X X n).arrow ≫ ((alternating_face_map_complex C).map f).f n) :=
by simp

@[simps]
def map {X Y : simplicial_object C} (f : X ⟶ Y) : obj X ⟶ obj Y :=
{ f := λ n, (obj_X Y n).factor_thru _ (map_factors_obj_X f n),
  comm' := λ i j hij, begin
    ext,
    simp only [obj_d, assoc, subobject.factor_thru_arrow, subobject.factor_thru_arrow_assoc],
    congr' 1,
    exact ((alternating_face_map_complex C).map f).comm i j,
  end, }

end degenerate_subcomplex

localized "notation `D[`X`]` := algebraic_topology.degenerate_subcomplex.obj X" in dold_kan

variable (C)

@[simps]
def degenerate_subcomplex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := degenerate_subcomplex.obj,
  map := λ X Y, degenerate_subcomplex.map, }

variable {C}

@[simps]
def inclusion_of_degenerate_subcomplex_app (X : simplicial_object C) :
  (degenerate_subcomplex C).obj X ⟶ (alternating_face_map_complex C).obj X :=
{ f := λ n, (degenerate_subcomplex.obj_X X n).arrow, }

variable (C)

@[simps]
def inclusion_of_degenerate_subcomplex :
  degenerate_subcomplex C ⟶ alternating_face_map_complex C :=
{ app := inclusion_of_degenerate_subcomplex_app, }

variable {C}

@[simps]
def Q_infty_to_degenerate_subcomplex (X : simplicial_object C) : K[X] ⟶ D[X] :=
{ f := λ n, (degenerate_subcomplex.obj_X X n).factor_thru (Q_infty.f n)
    (by rw [degenerate_subcomplex.obj_X_factors_iff_comp_P_infty_eq_zero,
      Q_infty_f_comp_P_infty_f]),
  comm' := λ i j hij, begin
    ext,
    simp only [degenerate_subcomplex.obj_d, assoc, subobject.factor_thru_arrow,
      subobject.factor_thru_arrow_assoc, homological_complex.hom.comm],
  end, }

instance : has_binary_biproducts (chain_complex C ℕ) := sorry

@[simp, reassoc]
lemma Q_infty_to_degenerate_subcomplex_comp_inclusion_of_degenerate_subcomplex_app
  (X : simplicial_object C) :
  Q_infty_to_degenerate_subcomplex X ≫ inclusion_of_degenerate_subcomplex_app X = Q_infty :=
by tidy

/-- `inclusion_of_degenerate_subcomplex_app X` is a split mono. -/
def split_mono_inclusion_of_degenerate_subcomplex_app (X : simplicial_object C) :
  split_mono (inclusion_of_degenerate_subcomplex_app X) :=
{ retraction := Q_infty_to_degenerate_subcomplex X, }

@[simp, reassoc]
lemma decomposition_KND₁₁ (X : simplicial_object C) :
  inclusion_of_Moore_complex_map X ≫ P_infty_to_normalized_Moore_complex X = 𝟙 N[X] :=
(split_mono_inclusion_of_Moore_complex_map X).id

@[simp, reassoc]
lemma decomposition_KND₂₁ (X : simplicial_object C) :
  inclusion_of_Moore_complex_map X ≫ Q_infty_to_degenerate_subcomplex X = 0 :=
begin
  ext n,
  simpa only [homological_complex.comp_f, Q_infty_to_degenerate_subcomplex_f, assoc,
    subobject.factor_thru_arrow, homological_complex.zero_f_apply, zero_comp]
    using homological_complex.congr_hom (inclusion_of_Moore_complex_map_comp_Q_infty X) n,
end

@[simp, reassoc]
lemma decomposition_KND₁₂ (X : simplicial_object C) :
  inclusion_of_degenerate_subcomplex_app X ≫ P_infty_to_normalized_Moore_complex X = 0 :=
begin
  ext n,
  simp only [homological_complex.comp_f, assoc, P_infty_to_normalized_Moore_complex_f,
    subobject.factor_thru_arrow, homological_complex.zero_f_apply, zero_comp,
    inclusion_of_degenerate_subcomplex_app_f, degenerate_subcomplex.obj_X_arrow_comp_P_infty],
end

@[simp, reassoc]
lemma decomposition_KND₂₂ (X : simplicial_object C) :
  inclusion_of_degenerate_subcomplex_app X ≫ Q_infty_to_degenerate_subcomplex X = 𝟙 D[X] :=
(split_mono_inclusion_of_degenerate_subcomplex_app X).id

def decomposition_K_N_D (X : simplicial_object C) : K[X] ≅ N[X] ⊞ D[X] :=
{ hom := biprod.lift (P_infty_to_normalized_Moore_complex X)
    (Q_infty_to_degenerate_subcomplex X),
  inv := biprod.desc (inclusion_of_Moore_complex_map X)
    (inclusion_of_degenerate_subcomplex_app X),
  hom_inv_id' := by simp only [biprod.lift_desc, P_infty_add_Q_infty,
    P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map,
    Q_infty_to_degenerate_subcomplex_comp_inclusion_of_degenerate_subcomplex_app],
  inv_hom_id' := by { ext1; ext1; simp, }, }

end algebraic_topology
