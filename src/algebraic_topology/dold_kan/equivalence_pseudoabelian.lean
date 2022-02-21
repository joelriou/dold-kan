/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_additive
import for_mathlib.idempotents.simplicial_object
import for_mathlib.idempotents.homological_complex

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

variables {C : Type*} [category C] [additive_category C] [is_idempotent_complete C]

namespace category_theory

namespace idempotents

namespace dold_kan

open algebraic_topology.dold_kan

def κ := to_karoubi (simplicial_object C)
instance e : is_equivalence κ := to_karoubi_is_equivalence (simplicial_object C)
def κequiv : equivalence (simplicial_object C) _ := functor.as_equivalence κ
def κinv : _ ⥤ simplicial_object C := κequiv.inverse

def κ' := to_karoubi (chain_complex C ℕ)
instance e' : is_equivalence κ' := to_karoubi_is_equivalence (chain_complex C ℕ)
def κequiv' : equivalence (chain_complex C ℕ) _ := functor.as_equivalence κ'
def κinv' : _ ⥤ chain_complex C ℕ := κequiv'.inverse

def N : simplicial_object C ⥤ chain_complex C ℕ :=
N' ⋙ κinv'

def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ'

lemma Γ_comp_κ : (Γ : chain_complex C ℕ ⥤ _) ⋙ κ = κ' ⋙ preadditive.dold_kan.Γ :=
congr_obj (functor_extension''_comp_whiskering_left_to_karoubi _ _).symm Γ'

def equivalence₀ : simplicial_object C ≌ karoubi (chain_complex C ℕ) :=
κequiv.trans preadditive.dold_kan.equivalence

lemma equivalence₀_functor : equivalence₀.functor = (N' : simplicial_object C ⥤ _) :=
congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _) N'

lemma equivalence₀_inverse :
  equivalence₀.inverse = (preadditive.dold_kan.Γ : karoubi (chain_complex C ℕ) ⥤ _) ⋙ κinv := by refl

def equivalence₁ : simplicial_object C ≌ karoubi (chain_complex C ℕ) :=
begin
  let F := (preadditive.dold_kan.Γ : karoubi (chain_complex C ℕ) ⥤ _) ⋙ κinv,
  let G := (N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)),
  letI : is_equivalence G := is_equivalence_of_iso (eq_to_iso equivalence₀_functor)
    (is_equivalence.of_equivalence equivalence₀),
  exact G.as_equivalence,
end

lemma equivalence₁_functor : equivalence₁.functor = (N' : simplicial_object C ⥤ _) := by refl
lemma equivalence₁_inverse :
  equivalence₀.inverse = (preadditive.dold_kan.Γ : karoubi (chain_complex C ℕ) ⥤ _) ⋙ κinv := by refl

def equivalence₂ : simplicial_object C ≌ chain_complex C ℕ :=
equivalence₁.trans κequiv'.symm

lemma equivalence₂_functor : equivalence₂.functor = (N : simplicial_object C ⥤ _) := by refl
lemma equivalence₂_inverse : equivalence₂.inverse = (κ' : chain_complex C ℕ ⥤ _) ⋙
  preadditive.dold_kan.Γ ⋙ κinv := by refl

lemma equivalence₂_inverse' : equivalence₂.inverse ≅ (Γ : chain_complex C ℕ ⥤  _) :=
begin
  calc equivalence₂.inverse ≅ ((κ' : chain_complex C ℕ ⥤ _) ⋙ preadditive.dold_kan.Γ) ⋙ κinv : by refl
  ... ≅ (Γ' ⋙ κ) ⋙ κinv : iso_whisker_right (eq_to_iso (Γ_comp_κ.symm)) _
  ... ≅ Γ' ⋙ (κ ⋙ κinv) : by refl
  ... ≅ Γ' ⋙ 𝟭 _ : iso_whisker_left _ κequiv.unit_iso.symm
  ... ≅ Γ : by refl,
end

def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
begin
  letI : is_equivalence (Γ : chain_complex C ℕ ⥤ _) :=
    is_equivalence_of_iso equivalence₂_inverse' (is_equivalence.of_equivalence equivalence₂.symm),
  exact Γ.as_equivalence.symm,
end

lemma equivalence_functor : (equivalence : simplicial_object C ≌ _ ).functor = N := by refl
lemma equivalence_inverse : (equivalence : simplicial_object C ≌ _ ).inverse = Γ := by refl

def NΓ : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) :=
begin
  calc Γ ⋙ N ≅ Γ' ⋙ N' ⋙ κinv' : by refl
  ... ≅ (Γ' ⋙ N') ⋙ κinv' : (functor.associator _ _ _).symm
  ... ≅ κ' ⋙ κinv' : iso_whisker_right NΓ' _
  ... ≅ 𝟭 _ : κequiv'.unit_iso.symm,
end

lemma NΓ_inv_objectwise (K : chain_complex C ℕ) :
NΓ.inv.app K = κequiv'.unit_iso.hom.app K ≫ κinv'.map (NΓ'.inv.app K) :=
by { dsimp only [NΓ, iso.refl, iso.trans], erw [comp_id, comp_id], refl, }

--lemma equivalence_unit_iso 




#exit
def unit_inv : (N' ⋙ κinv' ⋙ Γ) ⋙ κ ≅ (κ : simplicial_object C ⥤ _) :=
begin
  calc (N' ⋙ κinv' ⋙ Γ) ⋙ κ ≅ (N' ⋙ κinv') ⋙ (Γ ⋙ κ) : _
  ... ≅ (N' ⋙ κinv') ⋙ (κ' ⋙ γ) : iso_whisker_left _ _
  ... ≅ N' ⋙ (κinv' ⋙ κ') ⋙ γ : _
  ... ≅ N' ⋙ 𝟭 _ ⋙ γ : iso_whisker_left _ (iso_whisker_right eq'.counit_iso _)
  ... ≅ (N' ⋙ γ) : by refl
  ... ≅ κ : as_iso ΓN'_trans,
  { by refl, },
  { apply eq_to_iso,
    symmetry,
    exact congr_obj (functor_extension''_comp_whiskering_left_to_karoubi _ _) Γ', },
  { by refl, },
end

lemma unit_inv_objectwise (X : simplicial_object C) :
  unit_inv.hom.app X =
  eq_to_hom ((congr_obj (congr_obj
    (functor_extension''_comp_whiskering_left_to_karoubi _ _) Γ') ((N' ⋙ κinv').obj X)).symm) ≫
  γ.map (eq'.counit_iso.hom.app (N'_functor.obj X)) ≫ ΓN'_trans.app X :=
begin
  dsimp [unit_inv, iso.refl, iso.trans],
  simpa only [id_comp, comp_id, eq_to_hom_app, assoc],
end

def ΓN : N ⋙ Γ ≅ 𝟭 (simplicial_object C) :=
begin
  calc N ⋙ Γ ≅ (N' ⋙ κinv' ⋙ Γ) ⋙ 𝟭 _ : (functor.right_unitor _).symm
  ... ≅ (N' ⋙ κinv' ⋙ Γ) ⋙ (κ ⋙ κinv) : iso_whisker_left _ e.unit_iso
  ... ≅ ((N' ⋙ κinv' ⋙ Γ) ⋙ κ) ⋙ κinv : by refl
  ... ≅ κ ⋙ κinv : iso_whisker_right unit_inv _
  ... ≅ 𝟭 _ : e.unit_iso.symm,
end

lemma ΓN_hom_objectwise (X : simplicial_object C) :
ΓN.hom.app X = e.unit_iso.hom.app _ ≫ κinv.map (unit_inv.hom.app X) ≫ e.unit_iso.inv.app X :=
by { dsimp [ΓN], simpa only [id_comp, comp_id, assoc], }

lemma ΓN_trans_compat (Y : simplicial_object C) : ΓN_trans.app (κ.obj Y) =
  eq_to_hom
    (by { dsimp only [functor.comp], congr' 1,
      exact congr_obj (congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _) N') Y, }) ≫
  ΓN'_trans.app Y :=
begin
  erw [whiskering_left_to_karoubi_hom_equiv_inv_fun_compat, nat_trans.comp_app, eq_to_hom_app],
  refl,
end


@[simp]
def φ (Y : simplicial_object C) : (N' ⋙ κinv' ⋙ κ').obj Y ⟶ (N' ⋙ κinv' ⋙ Γ' ⋙ N').obj Y := NΓ'.inv.app (κinv'.obj (N'.obj Y))

@[simp]
def ψ (Y : simplicial_object C) : (N' ⋙ κinv' ⋙ Γ' ⋙ N').obj Y ⟶ N'.obj Y := N'.map (ΓN.hom.app Y)

lemma compat {D E : Type*} [category D] [category E] (e : D ≌ E) {A : E} {B : D} (φ : A ⟶ e.functor.obj B) :
  e.functor.map (e.inverse.map φ) ≫ e.functor.map (e.unit_iso.inv.app B) =
  e.counit_iso.hom.app A ≫ φ :=
begin
  erw ← e.counit_iso.hom.naturality φ,
  congr' 1,
  conv { to_lhs, rw ← comp_id (e.functor.map _), },
  erw [← e.functor_unit_iso_comp, ← assoc, ← e.functor.map_comp, ← nat_trans.comp_app,
    e.unit_iso.inv_hom_id, e.functor.map_id, id_comp],
  refl,
end



lemma conjugate_map_of_functor_eq {D E : Type*} [category D] [category E]
  {F G : D ⥤ E} (h : F = G) {X Y : D} (f : X ⟶ Y) :
  F.map f = eq_to_hom (by rw h) ≫ G.map f ≫ eq_to_hom (by rw h) :=
by { subst h, simp only [eq_to_hom_refl, id_comp, comp_id], }

lemma conjugate_app_of_obj_eq {D E : Type*} [category D] [category E]
  {F G : D ⥤ E} (φ : F ⟶ G) {X Y : D} (h : X = Y) :
  φ.app X = eq_to_hom (by rw h) ≫ φ.app Y ≫ eq_to_hom (by rw h) :=
by { subst h, simp only [eq_to_hom_refl, id_comp, comp_id], }


end dold_kan

end idempotents

end category_theory