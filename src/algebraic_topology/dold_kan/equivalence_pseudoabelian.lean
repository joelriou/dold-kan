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

def κ' := to_karoubi (chain_complex C ℕ)
instance e' : is_equivalence κ' := to_karoubi_is_equivalence (chain_complex C ℕ)
def eq' : equivalence (chain_complex C ℕ) _ := functor.as_equivalence κ'
def κinv' : _ ⥤ chain_complex C ℕ := eq'.inverse
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
  ... ≅ N' ⋙ 𝟭 _ ⋙ γ : iso_whisker_left _ (iso_whisker_right eq'.counit_iso _)
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
  ... ≅ 𝟭 _ : eq'.unit_iso.symm,
end

lemma NΓ_inv_objectwise (K : chain_complex C ℕ) :
NΓ.inv.app K = eq'.unit_iso.hom.app K ≫ 
κinv'.map (NΓ'.inv.app K) :=
begin
  dsimp only [NΓ, iso.refl, iso.trans],
  erw [comp_id, comp_id],
  refl,
end

@[simp]
def φ (Y : simplicial_object C) : (N' ⋙ κinv' ⋙ κ').obj Y ⟶ (N' ⋙ κinv' ⋙ Γ' ⋙ N').obj Y := NΓ'.inv.app (κinv'.obj (N'.obj Y))

@[simp]
def ψ (Y : simplicial_object C) : (N' ⋙ κinv' ⋙ Γ' ⋙ N').obj Y ⟶ N'.obj Y := N'.map (ΓN.hom.app Y)

theorem φ_comp_ψ (Y : simplicial_object C) : φ Y ≫ ψ Y = eq'.counit_iso.hom.app (N'.obj Y) :=
begin
  dsimp only [φ, ψ],
  rw ← NΓ_compat_NΓ',
  dsimp only [iso.trans, iso.refl, nat_iso.hcomp, nat_trans.hcomp, functor.right_unitor, eq_to_iso],
  simp only [nat_trans.comp_app, nat_trans.id_app, eq_to_hom_app],
  erw [id_comp, comp_id, assoc],
  have eq : algebraic_topology.dold_kan.N.obj (κ.obj Y) = N'.obj Y :=
    congr_obj (congr_obj (functor_extension'_comp_whiskering_left_to_karoubi (simplicial_object C) _) N') Y,
  let τ : _ ⟶ (N' ⋙ κinv' ⋙ κ').obj Y := eq_to_hom eq ≫ eq'.counit_iso.symm.hom.app (N'.obj Y),
  have h₁ := algebraic_topology.dold_kan.NΓ.inv.naturality τ,
  have h₂ := congr_arg (category_struct.comp (inv τ)) h₁,
  erw [← assoc, is_iso.inv_hom_id τ, id_comp] at h₂,
  erw [h₂, assoc, is_iso.inv_comp_eq τ],
  dsimp only [τ],
  simp only [assoc],
  have h₃ := congr_app eq'.counit_iso.inv_hom_id (N'.obj Y),
  rw nat_trans.comp_app at h₃,
  conv { to_rhs, erw [h₃, comp_id, ← id_comp (eq_to_hom eq), ← identity_N_objectwise (κ.obj Y), assoc], },
  congr' 1,
  clear h₃ h₂ h₁ τ,

  sorry
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
    have h := congr_map κinv' (φ_comp_ψ X),
    simp only [φ, ψ, κinv'.map_comp] at h,
    have h' := congr_map κinv' (congr_app eq'.counit_iso.inv_hom_id (N'.obj X)),
    erw [κinv'.map_comp, κinv'.map_id] at h',
    erw [← h', ← h],
    slice_rhs 1 2 { erw ← κinv'.map_comp, },
    congr,
    erw [κinv'.map_comp, NΓ_inv_objectwise],
    congr,
    exact equivalence.unit_app_inverse eq' (N'.obj X),
  end, }

end dold_kan

end idempotents

end category_theory