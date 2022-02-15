/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_additive

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

variables {C : Type*} [category C] [additive_category C] [is_idempotent_complete C]

namespace category_theory

namespace idempotents

namespace dold_kan

open algebraic_topology.dold_kan

instance : is_idempotent_complete (chain_complex C ℕ) := by sorry
instance : is_idempotent_complete (simplicial_object C) := by sorry

def N : simplicial_object C ⥤ chain_complex C ℕ :=
N' ⋙ (to_karoubi_is_equivalence (chain_complex C ℕ)).inverse

def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ'

def ΓN : N ⋙ Γ ≅ 𝟭 (simplicial_object C) :=
begin
  let κ := to_karoubi (simplicial_object C),
  let κ' := to_karoubi (chain_complex C ℕ),
  let κinv := is_equivalence.inverse κ,
  let κinv' := is_equivalence.inverse κ',
  let e := to_karoubi_is_equivalence (simplicial_object C),
  let e' := to_karoubi_is_equivalence (chain_complex C ℕ),
  let γ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) := algebraic_topology.dold_kan.Γ,
  calc N ⋙ Γ ≅ (N ⋙ Γ) ⋙ 𝟭 _ : (functor.right_unitor _).symm
  ... ≅ (N ⋙ Γ) ⋙ (κ ⋙ κinv) : iso_whisker_left _ e.unit_iso
  ... ≅ (N' ⋙ κinv') ⋙ Γ' ⋙ (κ ⋙ κinv) : by refl
  ... ≅ (N' ⋙ κinv') ⋙ (Γ' ⋙ κ) ⋙ κinv : iso_whisker_left _ (functor.associator _ _ _).symm
  ... ≅ (N' ⋙ κinv') ⋙ (κ' ⋙ γ) ⋙ κinv : iso_whisker_left _ (iso_whisker_right _ _)
  ... ≅ N' ⋙ (κinv' ⋙ κ') ⋙ (γ ⋙ κinv) : by refl
  ... ≅ N' ⋙ 𝟭 _ ⋙ (γ ⋙ κinv) : iso_whisker_left _ (iso_whisker_right e'.counit_iso _)
  ... ≅ N' ⋙ (γ ⋙ κinv) : iso_whisker_left _ (functor.left_unitor _)
  ... ≅ (N' ⋙ γ) ⋙ κinv : (functor.associator _ _ _).symm
  ... ≅ (𝟭 _ ⋙ κ) ⋙ κinv : iso_whisker_right (as_iso ΓN'_trans) _
  ... ≅ 𝟭 _ ⋙ κ ⋙ κinv : functor.associator _ _ _
  ... ≅ κ ⋙ κinv : functor.left_unitor _ 
  ... ≅ 𝟭 _ : e.unit_iso.symm,
  { apply eq_to_iso,
    symmetry,
    exact congr_obj (functor_extension''_comp_whiskering_left_to_karoubi _ _) Γ', },
end

def NΓ : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) :=
begin
  let κ' := to_karoubi (chain_complex C ℕ),
  let κinv' := is_equivalence.inverse κ',
  let e' := to_karoubi_is_equivalence (chain_complex C ℕ),
  let γ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) := algebraic_topology.dold_kan.Γ,
  let ν : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) := algebraic_topology.dold_kan.N,
  calc Γ ⋙ N ≅ Γ ⋙ (N' ⋙ κinv') : iso.refl _
  ... ≅ (Γ ⋙ N') ⋙ κinv' : (functor.associator _ _ _).symm
  ... ≅ (κ' ⋙ γ ⋙ ν) ⋙ κinv' : iso_whisker_right _ _
  ... ≅ κ' ⋙ κinv' : iso_whisker_right algebraic_topology.dold_kan.NΓ' _
  ... ≅ 𝟭 _ : e'.unit_iso.symm,
  { apply eq_to_iso,
    have h := congr_obj (functor_extension''_comp_whiskering_left_to_karoubi (chain_complex C ℕ) _) Γ',
    have h' := congr_obj (functor_extension'_comp_whiskering_left_to_karoubi (simplicial_object C) _) N',
    dsimp at h h',
    conv { to_rhs, rw ← functor.assoc, congr, erw h, },
    rw functor.assoc,
    congr,
    exact h'.symm, }
end

@[simps]
def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
{ functor := N,
  inverse := Γ,
  unit_iso := ΓN.symm,
  counit_iso := NΓ,
  functor_unit_iso_comp' := λ X, begin

    sorry,
  end, }

end dold_kan

end idempotents

end category_theory