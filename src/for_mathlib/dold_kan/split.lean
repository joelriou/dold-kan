/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.split_simplicial_object
import for_mathlib.dold_kan.degenerate_subcomplex

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.preadditive opposite algebraic_topology.dold_kan
open_locale simplicial dold_kan big_operators

namespace simplicial_object

namespace splitting

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]
  {X : simplicial_object C} (s : splitting X)

def π_summand {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  X.obj Δ ⟶ s.N A.1.unop.len :=
begin
  refine (s.iso Δ).inv ≫ sigma.desc (λ B, _),
  by_cases B = A,
  { exact eq_to_hom (by { subst h, refl, }), },
  { exact 0, },
end

@[simp, reassoc]
lemma ι_π_summand_eq_id {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A ≫ s.π_summand A = 𝟙 _ :=
begin
  dsimp [ι_summand, π_summand],
  simp only [summand, assoc, is_iso.hom_inv_id_assoc],
  erw [colimit.ι_desc, cofan.mk_ι_app],
  dsimp,
  simp only [eq_self_iff_true, if_true],
end

@[simp, reassoc]
lemma ι_π_summand_eq_zero {Δ : simplex_categoryᵒᵖ} (A B : index_set Δ) (h : B ≠ A):
  s.ι_summand A ≫ s.π_summand B = 0 :=
begin
  dsimp [ι_summand, π_summand],
  simp only [summand, assoc, is_iso.hom_inv_id_assoc],
  erw [colimit.ι_desc, cofan.mk_ι_app],
  apply dif_neg,
  exact h.symm,
end

lemma decomposition_id (Δ : simplex_categoryᵒᵖ) :
  𝟙 (X.obj Δ) = ∑ (A : index_set Δ), s.π_summand A ≫ s.ι_summand A :=
begin
  apply s.hom_ext',
  intro A,
  rw [comp_id, comp_sum, finset.sum_eq_single A, ι_π_summand_eq_id_assoc],
  { intros B h₁ h₂,
    rw [s.ι_π_summand_eq_zero_assoc _ _ h₂, zero_comp], },
  { intro h,
    exfalso,
    simpa only [finset.mem_univ, not_true] using h, },
end

@[simp, reassoc]
lemma σ_comp_π_summand_id_eq_zero {n : ℕ} (i : fin (n+1)) :
  X.σ i ≫ s.π_summand (index_set.id (op [n+1])) = 0 :=
begin
  apply s.hom_ext',
  intro A,
  erw [comp_zero, s.ι_summand_epi_naturality_assoc A (simplex_category.σ i).op,
    ι_π_summand_eq_zero],
  symmetry,
  change ¬ (A.epi_comp (simplex_category.σ i).op).eq_id,
  rw index_set.eq_id_iff_len_eq,
  have h := simplex_category.len_le_of_epi (infer_instance : epi A.e),
  dsimp at ⊢ h,
  linarith,
end

lemma comp_P_infty_eq_zero_iff {Z : C} {n : ℕ} (f : Z ⟶ X _[n]) :
  f ≫ P_infty.f n = 0 ↔ f ≫ s.π_summand (index_set.id (op [n])) = 0 :=
begin
  split,
  { intro h,
    cases n,
    { dsimp at h,
      rw [comp_id] at h,
      rw [h, zero_comp], },
    { have h' := f ≫= P_infty_f_add_Q_infty_f (n+1),
      erw [comp_id, comp_add, h, zero_add] at h',
      rw [← h', assoc, Q_infty_f, decomposition_Q, preadditive.sum_comp,
        preadditive.comp_sum, finset.sum_eq_zero],
      intros i hi,
      simp only [assoc, σ_comp_π_summand_id_eq_zero, comp_zero], }, },
  { intro h,
    rw [← comp_id f, assoc, s.decomposition_id, preadditive.sum_comp,
      preadditive.comp_sum, fintype.sum_eq_zero],
    intro A,
    rw [assoc],
    by_cases hA : A.eq_id,
    { dsimp at hA,
      subst hA,
      rw [reassoc_of h, zero_comp], },
    { simp only [P_infty_on_splitting_eq_zero s A hA, comp_zero], }, },
end

@[simp]
def d (i j : ℕ) : s.N i ⟶ s.N j :=
s.ι_summand (index_set.id (op [i])) ≫ K[X].d i j ≫ s.π_summand (index_set.id (op [j]))

@[simps]
def N' : chain_complex C ℕ :=
{ X := s.N,
  d := s.d,
  shape' := λ i j hij, by simp only [d, K[X].shape i j hij, zero_comp, comp_zero],
  d_comp_d' := λ i j k hij hjk, begin
    simp only [d, assoc],
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op [j])) ≫ K[X].d j k ≫
      s.π_summand (index_set.id (op [k])) = 0 :=
      by erw [id_comp, homological_complex.d_comp_d_assoc, zero_comp],
    rw s.decomposition_id at eq,
    classical,
    rw [fintype.sum_eq_add_sum_compl (index_set.id (op [j])), add_comp, comp_add, assoc,
      preadditive.sum_comp, preadditive.comp_sum, finset.sum_eq_zero, add_zero] at eq,
    { rw [eq, comp_zero], },
    { intros A hA,
      simp only [finset.mem_compl, finset.mem_singleton] at hA,
      change ¬A.eq_id at hA,
      rw index_set.eq_id_iff_mono at hA,
      suffices : s.ι_summand A ≫ K[X].d j k ≫ s.π_summand (index_set.id (op [k])) = 0,
      { simp only [assoc, this, comp_zero], },
      change k+1 = j at hjk,
      subst hjk,
      simp only [s.ι_summand_eq, ← assoc, ← s.comp_P_infty_eq_zero_iff],
      simp only [assoc, ← P_infty.comm (k+1) k, P_infty_on_degeneracies_assoc X (k+1) A.e hA,
        zero_comp, comp_zero], },
  end }

end splitting

end simplicial_object
