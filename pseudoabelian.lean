/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.preadditive
import category_theory.limits.shapes.biproducts

/-!
# Pseudoabelian categories

-/

open category_theory
open category_theory.category
open category_theory.limits

noncomputable theory

open category_theory
open category_theory.preadditive

namespace category_theory

variables {C : Type*} [category C] [preadditive C]
variable {X : C}

class is_projector (p : X ⟶ X) : Prop := (idempotence : p ≫ p = p)

@[simp]
def binary_bicone_of_projector {X : C} (p : X ⟶ X)
  [h : is_projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
  binary_bicone (kernel (𝟙 X - p)) (kernel p) :=
{ X := X,
  inl := kernel.ι (𝟙 X - p),
  inr := kernel.ι p,
  fst := kernel.lift (𝟙 X - p) p 
    (by { rw [comp_sub, category.comp_id, sub_eq_zero], exact h.idempotence.symm, }),
  snd := kernel.lift p (𝟙 X - p)
    (by { rw [sub_comp, category.id_comp, sub_eq_zero], exact h.idempotence.symm, }),
  inl_snd' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
    assoc, kernel.lift_ι], },
  inr_fst' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
    assoc, kernel.lift_ι], },
  inl_fst' :=
  begin
    ext,
    rw [assoc, limits.kernel.lift_ι, limits.equalizer_as_kernel, id_comp],
    symmetry,
    conv { to_lhs, rw ← comp_id (kernel.ι _), },
    apply sub_eq_zero.mp,
    rw [← comp_sub, kernel.condition],
  end,
  inr_snd' := by { ext, rw [assoc, kernel.lift_ι, equalizer_as_kernel, id_comp, comp_sub,
      kernel.condition, sub_zero, comp_id], }, }

def binary_biproduct_data_of_projector {X : C} (p : X ⟶ X)
  [h : is_projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
  binary_biproduct_data (kernel (𝟙 X - p)) (kernel p) :=
  binary_biproduct_data_of_total
  { X := X,
    inl := kernel.ι (𝟙 X - p),
    inr := kernel.ι p,
    fst := kernel.lift (𝟙 X - p) p 
      (by { rw [comp_sub, category.comp_id, sub_eq_zero], exact h.idempotence.symm, }),
    snd := kernel.lift p (𝟙 X - p)
      (by { rw [sub_comp, category.id_comp, sub_eq_zero], exact h.idempotence.symm, }),
    inl_snd' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
      assoc, kernel.lift_ι], },
    inr_fst' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
      assoc, kernel.lift_ι], },
    inl_fst' :=
    begin
      ext,
      rw [assoc, limits.kernel.lift_ι, limits.equalizer_as_kernel, id_comp],
      symmetry,
      conv { to_lhs, rw ← comp_id (kernel.ι _), },
      apply sub_eq_zero.mp,
      rw [← comp_sub, kernel.condition],
    end,
    inr_snd' := by { ext, rw [assoc, kernel.lift_ι, equalizer_as_kernel, id_comp, comp_sub,
        kernel.condition, sub_zero, comp_id], }, }
  (by { dsimp [binary_bicone_of_projector], simp only [kernel.lift_ι, add_sub_cancel'_right], })

class is_pseudoabelian (C : Type*) [category C] [preadditive C] : Prop :=
(projectors_have_kernels : Π (X : C) (p : X ⟶ X), is_projector p → has_kernel p)

end category_theory
