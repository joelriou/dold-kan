/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.split_simplicial_object
import for_mathlib.dold_kan.degenerate_subcomplex

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.preadditive opposite
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

@[simp]
def d (i j : ℕ) : s.N i ⟶ s.N j :=
s.ι_summand (index_set.id (op [i])) ≫ K[X].d i j ≫ s.π_summand (index_set.id (op [j]))

@[simps]
def K : chain_complex C ℕ :=
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
      suffices : s.ι_summand A ≫ K[X].d j k ≫ s.π_summand (index_set.id (op [k])) = 0,
      { simp only [assoc, this, comp_zero], },
      change k+1 = j at hjk,
      subst hjk,
      rw [s.ι_summand_eq, assoc],
      sorry,
       },
  end }

end splitting

end simplicial_object
