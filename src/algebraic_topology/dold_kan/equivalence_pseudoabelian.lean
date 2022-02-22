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

def κequiv := to_karoubi_equivalence (simplicial_object C)
def κequiv' := to_karoubi_equivalence (chain_complex C ℕ)

def N : simplicial_object C ⥤ chain_complex C ℕ := N' ⋙ κequiv'.inverse

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

@[simps]
def η' : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N' ≅ κequiv'.functor := NΓ'

lemma hη : compatibility.τ₀ (eq_to_iso hN') (eq_to_iso hΓ) =
  compatibility.τ₁ (eq_to_iso hN') (eq_to_iso hΓ)
  (η' : _ ≅ (κequiv' : chain_complex C ℕ ≌ _ ).functor) :=
begin
  ext1, ext1, ext1 K,
  dsimp [compatibility.τ₀, compatibility.τ₁],
  simp only [id_comp, comp_id, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans],
  apply NΓ_karoubi_compat,
end

@[simps]
def η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) := compatibility.equivalence_counit_iso hη

lemma equivalence_counit_iso : dold_kan.equivalence.counit_iso = (η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ)) := 
compatibility.equivalence_counit_iso_eq hη

@[simps]
def ε' : κequiv.functor ≅ (N' : simplicial_object C ⥤ _) ⋙ preadditive.dold_kan.equivalence.inverse :=
(as_iso ΓN'_trans).symm

lemma hε : compatibility.υ (eq_to_iso hN') =
  (ε'.symm : _ ≅ (κequiv.functor : simplicial_object C ⥤ _ ) ) :=
begin
  ext1, apply nat_trans.ext, ext1 X,
  dsimp [compatibility.υ, ΓN, ε'],
  erw [comp_id, comp_id],
  simp only [eq_to_hom_app, eq_to_hom_map],
  symmetry,
  apply ΓN_trans_karoubi_compat,
end

@[simps]
def ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ :=
compatibility.equivalence_unit_iso (eq_to_iso hN') (eq_to_iso hΓ) ε'

lemma equivalence_unit_iso : dold_kan.equivalence.unit_iso = (ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ) := 
compatibility.equivalence_unit_iso_eq (eq_to_iso hN') (eq_to_iso hΓ) hε

end dold_kan

end idempotents

end category_theory