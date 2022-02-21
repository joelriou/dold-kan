/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_additive
import algebraic_topology.dold_kan.compatibility
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

def N : simplicial_object C ⥤ chain_complex C ℕ := N' ⋙ κinv'

def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ'

lemma hN' : κequiv.functor ⋙ preadditive.dold_kan.equivalence.functor =
  (N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _) N'

lemma hΓ :
  κequiv'.functor ⋙ preadditive.dold_kan.equivalence.inverse =
    (Γ : chain_complex C ℕ ⥤ _) ⋙ κequiv.functor  :=
congr_obj (functor_extension''_comp_whiskering_left_to_karoubi _ _) Γ'

def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
compatibility.equivalence (eq_to_iso hN') (eq_to_iso hΓ)

lemma equivalence_functor : (equivalence : simplicial_object C ≌ _ ).functor = N := by refl
lemma equivalence_inverse : (equivalence : simplicial_object C ≌ _ ).inverse = Γ := by refl

def η' : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N' ≅ κequiv'.functor := NΓ'

lemma hη : compatibility.τ₀ (eq_to_iso hN') (eq_to_iso hΓ) =
  compatibility.τ₁ (eq_to_iso hN') (eq_to_iso hΓ)
  (η' : _ ≅ (κequiv' : chain_complex C ℕ ≌ _ ).functor) := sorry


def η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) := compatibility.equivalence_counit_iso hη


lemma equivalence_counit_iso_eq : dold_kan.equivalence.counit_iso = (η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ)) := 
  compatibility.equivalence_counit_iso_eq hη

/-
def NΓ : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) :=
begin
  calc Γ ⋙ N ≅ Γ' ⋙ N' ⋙ κinv' : by refl
  ... ≅ (Γ' ⋙ N') ⋙ κinv' : (functor.associator _ _ _).symm
  ... ≅ κ' ⋙ κinv' : iso_whisker_right NΓ' _
  ... ≅ 𝟭 _ : κequiv'.unit_iso.symm,
end

lemma NΓ_hom_app (K : chain_complex C ℕ) :
NΓ.hom.app K = κinv'.map (NΓ'.hom.app K) ≫ κequiv'.unit_iso.inv.app K :=
by { dsimp only [NΓ, iso.refl, iso.trans, functor.associator], erw [id_comp, id_comp], refl }

lemma NΓ_inv_app (K : chain_complex C ℕ) :
NΓ.inv.app K = κequiv'.unit_iso.hom.app K ≫ κinv'.map (NΓ'.inv.app K) :=
by { dsimp only [NΓ, iso.refl, iso.trans], erw [comp_id, comp_id], refl, }

lemma equivalence_counit_iso :
  (dold_kan.equivalence.counit_iso : _ ≅ 𝟭 (chain_complex C ℕ)) = NΓ := sorry
-/

end dold_kan

end idempotents

end category_theory