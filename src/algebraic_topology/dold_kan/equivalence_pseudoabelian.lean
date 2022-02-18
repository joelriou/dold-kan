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

private def e' := to_karoubi_is_equivalence (chain_complex C ℕ)
private def κ' := to_karoubi (chain_complex C ℕ)
private def κinv' : _ ⥤ chain_complex C ℕ := e'.inverse
private def e := to_karoubi_is_equivalence (simplicial_object C)
private def κ := to_karoubi (simplicial_object C)
private def κinv : _ ⥤ simplicial_object C := e.inverse
private def γ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) := algebraic_topology.dold_kan.Γ

def N : simplicial_object C ⥤ chain_complex C ℕ :=
N' ⋙ κinv'

def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ'

def unit_inv : (N' ⋙ κinv' ⋙ Γ) ⋙ κ ≅ (κ : simplicial_object C ⥤ _) :=
begin
  calc (N' ⋙ κinv' ⋙ Γ) ⋙ κ ≅ (N' ⋙ κinv') ⋙ (Γ ⋙ κ) : _
  ... ≅ (N' ⋙ κinv') ⋙ (κ' ⋙ γ) : iso_whisker_left _ _
  ... ≅ N' ⋙ (κinv' ⋙ κ') ⋙ γ : _
  ... ≅ N' ⋙ 𝟭 _ ⋙ γ : iso_whisker_left _ (iso_whisker_right e'.counit_iso _)
  ... ≅ (N' ⋙ γ) : by refl
  ... ≅ κ : as_iso ΓN'_trans,
  { by refl, },
  { apply eq_to_iso,
    symmetry,
    exact congr_obj (functor_extension''_comp_whiskering_left_to_karoubi _ _) Γ', },
  { by refl, },
end

def ΓN : N ⋙ Γ ≅ 𝟭 (simplicial_object C) :=
begin
  calc N ⋙ Γ ≅ (N' ⋙ κinv' ⋙ Γ) ⋙ 𝟭 _ : (functor.right_unitor _).symm
  ... ≅ (N' ⋙ κinv' ⋙ Γ) ⋙ (κ ⋙ κinv) : iso_whisker_left _ e.unit_iso
  ... ≅ ((N' ⋙ κinv' ⋙ Γ) ⋙ κ) ⋙ κinv : by refl
  ... ≅ κ ⋙ κinv : iso_whisker_right unit_inv _
  ... ≅ 𝟭 _ : e.unit_iso.symm,
end

def NΓ : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) :=
begin
  calc Γ ⋙ N ≅ Γ' ⋙ N' ⋙ κinv' : by refl
  ... ≅ (Γ' ⋙ N') ⋙ κinv' : (functor.associator _ _ _).symm
  ... ≅ κ' ⋙ κinv' : iso_whisker_right NΓ' _
  ... ≅ 𝟭 _ : e'.unit_iso.symm,
end

@[simps]
def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
{ functor := N,
  inverse := Γ,
  unit_iso := ΓN.symm,
  counit_iso := NΓ,
  functor_unit_iso_comp' := λ X, begin
    let α := ΓN.app X,
    let β := NΓ.app (N.obj X),
    have hα : N.map (ΓN.symm.hom.app X) = (N.map_iso α).inv := by refl,
    have hβ : NΓ.hom.app (N.obj X) = β.hom := by refl,
    rw [hα, hβ, iso.inv_comp_eq],
    symmetry,
    erw [comp_id, ← comp_id β.hom, ← iso.inv_comp_eq],
    dsimp [α, β],
    clear hα hβ α β,
    sorry,
  end, }

end dold_kan

end idempotents

end category_theory