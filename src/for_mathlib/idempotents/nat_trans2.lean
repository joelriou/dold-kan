/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.idempotents.functor_extension2
import category_theory.natural_isomorphism

import category_theory.functor.fully_faithful

open category_theory.category
open category_theory.idempotents
open category_theory.idempotents.karoubi

namespace category_theory

namespace idempotents

variables {C D : Type*} [category C] [category D]

@[simps]
def karoubi.equiv_map (X Y : C) : (X ⟶ Y) ≃ ((to_karoubi C).obj X ⟶ (to_karoubi C).obj Y) :=
{ to_fun := λ f, (to_karoubi C).map f,
  inv_fun := λ f, f.f,
  left_inv := by tidy,
  right_inv := by tidy, }

@[simps]
def whiskering_right_to_karoubi_hom_equiv
  (F G : C ⥤ D) : (F ⟶ G) ≃ (F ⋙ to_karoubi D ⟶ G ⋙ to_karoubi D) :=
{ to_fun := λ φ,
  { app := λ X, (karoubi.equiv_map _ _ ).to_fun (φ.app X), },
  inv_fun := λ ψ,
  { app := λ X, (karoubi.equiv_map _ _ ).inv_fun (ψ.app X),
    naturality' := λ X Y f, by simpa only [hom_ext] using nat_trans.naturality ψ f, },
  left_inv := by tidy,
  right_inv := by tidy, }

@[simps]
def whiskering_right_to_karoubi_iso_equiv
  (F G : C ⥤ D) : (F ≅ G) ≃ (F ⋙ to_karoubi D ≅ G ⋙ to_karoubi D) :=
{ to_fun := λ e, iso_whisker_right e (to_karoubi D),
  inv_fun := λ e,
  { hom := (whiskering_right_to_karoubi_hom_equiv F G).inv_fun e.hom,
    inv := (whiskering_right_to_karoubi_hom_equiv G F).inv_fun e.inv,
    hom_inv_id' := by { ext X, simpa only [hom_ext, iso.app_inv] using (e.app X).hom_inv_id, },
    inv_hom_id' := by { ext X, simpa only [iso.app_hom, hom_ext] using (e.app X).inv_hom_id, }, },
  left_inv := by tidy,
  right_inv := by tidy, }

end idempotents

end category_theory
