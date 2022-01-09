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

namespace pseudoabelian

variables {C : Type*} [category C] [preadditive C]
variable {X : C}

class projector (p : X ⟶ X) : Prop := (idempotence : p ≫ p = p)

@[simp]
def binary_bicone_of_projector {X : C} (p : X ⟶ X)
  [h : projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
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
  [h : projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
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

class is_pseudoabelian : Prop :=
(projectors_have_kernels : Π (X : C) (p : X ⟶ X), projector p → has_kernel p)

variables (C)

structure karoubi := (X : C) (p : X ⟶ X) (idempotence : p ≫ p = p)

namespace karoubi

variables {C}

def hom (P Q : karoubi C) := { f : P.X ⟶ Q.X // f = P.p ≫ f ≫ Q.p }

@[ext]
lemma hom_ext {P Q : karoubi C} (f' g' : hom P Q) : f'.1 = g'.1 → f' = g' :=
by { intro h, cases f', cases g', simpa only [subtype.mk_eq_mk] using h, }

@[simp]
def id (P : karoubi C) : hom P P := ⟨P.p, by repeat { rw P.idempotence, }⟩

lemma comp_p {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.1 = f.1 :=
by { rw [f.2, ← assoc, P.idempotence], }

lemma p_comp {P Q : karoubi C} (f : hom P Q) : f.1 ≫ Q.p = f.1 :=
by { rw [f.2, assoc, assoc, Q.idempotence], }

@[simp]
def comp {P Q R : karoubi C} (g' : hom Q R) (f' : hom P Q) : hom P R :=
  ⟨f'.1 ≫ g'.1, by rw [assoc, p_comp, ← assoc, comp_p], ⟩

end karoubi

instance : category (karoubi C) :=
{ hom      := karoubi.hom,
  id       := karoubi.id,
  comp     := λ P Q R f' g', karoubi.comp g' f',
  id_comp' := λ P Q f', by { ext, simp only [karoubi.id, karoubi.comp, karoubi.comp_p], },
  comp_id' := λ P Q f', by { ext, simp only [karoubi.id, karoubi.comp, karoubi.p_comp], },
  assoc'   := λ P Q R S f' g' h', by { ext, simp only [category.assoc, karoubi.comp], }, }

instance karoubi_coe : has_coe C (karoubi C) := ⟨λ X, ⟨X, 𝟙 X, by rw comp_id⟩⟩

@[simp]
lemma karoubi_coe_X (X : C) : (X : karoubi C).X = X := by refl

@[simp]
lemma karoubi_coe_p (X : C) : (X : karoubi C).p = 𝟙 X := by refl

def to_karoubi : C ⥤ karoubi C := {
  obj := λ X, ⟨X, 𝟙 X, by rw comp_id⟩,
  map := λ X Y f, ⟨f, by simp only [comp_id, id_comp]⟩ }

--instance : preadditive (karoubi C) := ⟨ λ P Q, begin sorry end ⟩
-- additive_category si C l'est
-- pseudoab
-- to_karoubi est une equiv sssi C est pseudoab

end pseudoabelian

end category_theory
