/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_additive
import algebraic_topology.dold_kan.compatibility
import for_mathlib.idempotents.simplicial_object

/-!

# The Dold-Kan correspondence for pseudoabelian categories

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

variables {C : Type*} [category C] [additive_category C] [is_idempotent_complete C]

namespace category_theory

namespace idempotents

namespace dold_kan

open algebraic_topology.dold_kan

/-- The equivalence `simplicial_object A ≌ karoubi (simplicial_object A) ` -/
@[nolint unused_arguments]
def κequiv := to_karoubi_equivalence (simplicial_object C)

/-- The equivalence `chain_complex A ℕ ≌ karoubi (chain_complex A ℕ) ` -/
def κequiv' := to_karoubi_equivalence (chain_complex C ℕ)

/-- The functor `N` for the equivalence is obtained by composing
`N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)` and the inverse
of the equivalence `chain_complex C ℕ ≌ karoubi (chain_complex C ℕ)`. -/
@[simps]
def N : simplicial_object C ⥤ chain_complex C ℕ := N' ⋙ κequiv'.inverse

/-- The functor `Γ` for the equivalence is `Γ'`. -/
@[simps, nolint unused_arguments]
def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ₀

lemma hN' : κequiv.functor ⋙ preadditive.dold_kan.equivalence.functor =
  (N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
congr_obj (functor_extension'_comp_whiskering_left_to_karoubi _ _) N'

lemma hΓ : κequiv'.functor ⋙ preadditive.dold_kan.equivalence.inverse =
    (Γ : chain_complex C ℕ ⥤ _) ⋙ κequiv.functor  :=
congr_obj (functor_extension''_comp_whiskering_left_to_karoubi _ _) Γ₀

/-- The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`compatibility.lean` to the equivalence `preadditive.dold_kan.equivalence`. -/
def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
compatibility.equivalence (eq_to_iso hN') (eq_to_iso hΓ)

lemma equivalence_functor : (equivalence : simplicial_object C ≌ _ ).functor = N := by refl
lemma equivalence_inverse : (equivalence : simplicial_object C ≌ _ ).inverse = Γ := by refl

/-- The natural isomorphism `NΓ' satisfies the compatibility that is needed
for the construction of our counit isomorphism `η` -/
lemma hη : compatibility.τ₀ =
  compatibility.τ₁ (eq_to_iso hN') (eq_to_iso hΓ)
  (NΓ' : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N' ≅ κequiv'.functor) :=
begin
  ext1, ext1, ext1 K,
  rw compatibility.τ₀_hom_app_eq,
  dsimp [compatibility.τ₁],
  simp only [id_comp, comp_id, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans],
  apply NΓ_karoubi_compat,
end

/-- The counit isomorphism induced by `NΓ'` -/
@[simps]
def η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) := compatibility.equivalence_counit_iso
  (NΓ' : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N' ≅ κequiv'.functor)

lemma equivalence_counit_iso :
  dold_kan.equivalence.counit_iso = (η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ)) :=
compatibility.equivalence_counit_iso_eq hη

lemma hεinv : compatibility.υ (eq_to_iso hN') =
  as_iso (ΓN'_trans : (N' : simplicial_object C ⥤ _) ⋙
  preadditive.dold_kan.equivalence.inverse ⟶ κequiv.functor) :=
begin
  symmetry,
  ext1, apply nat_trans.ext, ext1 X,
  dsimp [compatibility.υ, ΓN],
  erw [comp_id, comp_id],
  simp only [eq_to_hom_app, eq_to_hom_map],
  apply ΓN_trans_karoubi_compat,
end

/-- The unit isomorphism induced by `ΓN'_trans` -/
@[simps]
def ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ :=
compatibility.equivalence_unit_iso (eq_to_iso hΓ) (as_iso ΓN'_trans)

lemma equivalence_unit_iso : dold_kan.equivalence.unit_iso =
  (ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ) :=
compatibility.equivalence_unit_iso_eq hεinv

end dold_kan

end idempotents

end category_theory
