/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.idempotents.functor_extension
import category_theory.natural_isomorphism

import category_theory.functor.fully_faithful

open category_theory.category
open category_theory.idempotents
open category_theory.idempotents.karoubi

namespace category_theory

namespace idempotents

variables {C D : Type*} [category C] [category D]

@[simps]
def whiskering_left_to_karoubi_hom_equiv
  (F G : karoubi C ⥤ D) : (F ⟶ G) ≃ (to_karoubi _ ⋙ F ⟶ to_karoubi _ ⋙ G) :=
{ to_fun := λ φ,
  { app := λ X, φ.app ((to_karoubi C).obj X),
    naturality' := λ X Y f, by simp only [nat_trans.naturality, functor.comp_map], },
  inv_fun := λ ψ,
  { app := λ P, F.map (decomp_id_i P) ≫ (ψ.app P.X) ≫ G.map (decomp_id_p P),
    naturality' := λ P Q f, by {
      slice_lhs 1 2 { rw [← F.map_comp], },
      slice_rhs 3 4 { rw [← G.map_comp], },
      rw [decomp_id_i_naturality, decomp_id_p_naturality,
        F.map_comp, G.map_comp],
      slice_lhs 2 3 { erw ψ.naturality, },
      simp only [assoc],
      refl, }, },
  left_inv := λ φ, by { ext P, exact (nat_trans_eq φ P).symm, },
  right_inv := λ ψ, begin
    ext X,
    dsimp,
    erw [decomp_id_i_to_karoubi, decomp_id_p_to_karoubi,
      F.map_id, G.map_id, comp_id, id_comp],
  end }

lemma whiskering_left_to_karoubi_hom_inv_fun_comp
  {F G H : karoubi C ⥤ D} (φ : to_karoubi _ ⋙ F ⟶ to_karoubi _ ⋙ G)
  (ψ : to_karoubi _ ⋙ G ⟶ to_karoubi _ ⋙  H) :
  (whiskering_left_to_karoubi_hom_equiv F H).inv_fun (φ ≫ ψ) =
  (whiskering_left_to_karoubi_hom_equiv F G).inv_fun φ ≫
  (whiskering_left_to_karoubi_hom_equiv G H).inv_fun ψ :=
begin
  ext P,
  dsimp,
  slice_rhs 3 4 { rw [← G.map_comp, ← decomp_p], },
  erw ψ.naturality P.p,
  slice_rhs 4 5 { erw [← H.map_comp], },
  simp only [assoc],
  congr,
  ext,
  simp only [decomp_id_p_f, comp, to_karoubi_map_f, P.idem],
end

lemma whiskering_left_to_karoubi_hom_inv_fun_id
  {F : karoubi C ⥤ D} :
  (whiskering_left_to_karoubi_hom_equiv F F).inv_fun (𝟙 _) = 𝟙 _ :=
begin
  ext P,
  simp only [whiskering_left_to_karoubi_hom_equiv_symm_apply_app, nat_trans.id_app, equiv.inv_fun_as_coe],
  erw [id_comp, ← F.map_comp, ← decomp_id, F.map_id],
end

@[simps]
def whiskering_left_to_karoubi_iso_equiv
  (F G : karoubi C ⥤ D) : (F ≅ G) ≃ (to_karoubi _ ⋙ F ≅ to_karoubi _ ⋙ G) :=
{ to_fun := λ φ,
  { hom := (whiskering_left_to_karoubi_hom_equiv F G).to_fun φ.hom,
    inv := (whiskering_left_to_karoubi_hom_equiv G F).to_fun φ.inv, },
  inv_fun := λ ψ,
  { hom := (whiskering_left_to_karoubi_hom_equiv F G).inv_fun ψ.hom,
    inv := (whiskering_left_to_karoubi_hom_equiv G F).inv_fun ψ.inv,
    hom_inv_id' := by rw [← whiskering_left_to_karoubi_hom_inv_fun_comp, iso.hom_inv_id, whiskering_left_to_karoubi_hom_inv_fun_id],
    inv_hom_id' := by rw [← whiskering_left_to_karoubi_hom_inv_fun_comp, iso.inv_hom_id, whiskering_left_to_karoubi_hom_inv_fun_id], },
  left_inv := λ φ, by { ext P, simp only [equiv.to_fun_as_coe, equiv.symm_apply_apply,
    equiv.inv_fun_as_coe], },
  right_inv := λ ψ, by { ext X, simp only [equiv.to_fun_as_coe, equiv.apply_symm_apply,
    equiv.inv_fun_as_coe], } }

lemma karoubi_universal₁_inverse_preimage (F G : karoubi C ⥤ karoubi D)
  (φ : ((karoubi_universal₁ C D).inverse).obj F ⟶ ((karoubi_universal₁ C D).inverse).obj G) :
  (karoubi_universal₁ C D).inverse.preimage φ = (whiskering_left_to_karoubi_hom_equiv F G).inv_fun φ :=
begin
  apply functor.map_injective (((whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C))),
  erw functor.image_preimage,
  ext1, ext1 X,
  dsimp [decomp_id_i, decomp_id_p],
  erw [F.map_id, G.map_id, id_comp, comp_id],
end

--lemma karoubi_universal'_inverse_preimage_iso (F G : karoubi C ⥤ karoubi D)
--  (e : ((karoubi_universal' C D).inverse).obj F ≅ ((karoubi_universal' C D).inverse).obj G) :
--  preimage_iso e = (whiskering_left_to_karoubi_iso_equiv F G).inv_fun e :=
--by { ext1, exact karoubi_universal'_inverse_preimage F G e.hom, }

lemma whiskering_left_to_karoubi_hom_equiv_inv_fun_compat {F G : karoubi C ⥤ D}
  (ψ : to_karoubi _ ⋙ F ⟶ to_karoubi _ ⋙ G) (X : C) :
  ((whiskering_left_to_karoubi_hom_equiv _ _).inv_fun ψ).app ((to_karoubi _).obj X) = ψ.app X :=
congr_app ((whiskering_left_to_karoubi_hom_equiv _ _).right_inv ψ) X

end idempotents

end category_theory
