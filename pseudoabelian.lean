/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.preadditive
import category_theory.limits.shapes.biproducts
import category_theory.limits.shapes.kernels

/-!
# Pseudoabelian categories

-/

open category_theory
open category_theory.preadditive
open category_theory.limits

noncomputable theory

open category_theory
open category_theory.preadditive

namespace category_theory

variables {C : Type*} [category C] [preadditive C]
variable {X : C}

class is_projector (p : X ⟶ X) : Prop := (idempotence : p ≫ p = p)

def binary_bicone_of_projector {X : C} (p : X ⟶ X)
  [h : is_projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
  binary_bicone (kernel (𝟙 X - p)) (kernel p) :=
{ X := X,
  fst := kernel.lift (𝟙 X - p) p 
    (by { rw [comp_sub, category.comp_id, sub_eq_zero], exact h.idempotence.symm, }),
  snd := kernel.lift p (𝟙 X - p)
    (by { rw [sub_comp, category.id_comp, sub_eq_zero], exact h.idempotence.symm, }),
  inl := kernel.ι (𝟙 X - p),
  inr := kernel.ι p,
  inl_snd' := by { dsimp, ext, simp only [limits.zero_comp, limits.kernel.condition,
      category.assoc, limits.kernel.lift_ι], },
  inr_fst' := by { dsimp, ext, simp only [limits.zero_comp, limits.kernel.condition,
      category.assoc, limits.kernel.lift_ι], },
  inl_fst' := sorry,
  inr_snd' := sorry,
}

class is_pseudoabelian (C : Type*) [category C] [preadditive C] : Prop :=
(projectors_have_kernels : Π (X : C) (p : X ⟶ X), is_projector p → has_kernel p)

end category_theory
