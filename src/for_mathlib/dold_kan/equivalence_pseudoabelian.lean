/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.equivalence_additive
import for_mathlib.dold_kan.compatibility
import for_mathlib.idempotents.simplicial_object

/-!

# The Dold-Kan correspondence for pseudoabelian categories

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]
  [is_idempotent_complete C]

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
def N : simplicial_object C ⥤ chain_complex C ℕ := N₁ ⋙ κequiv'.inverse

/-- The functor `Γ` for the equivalence is `Γ'`. -/
@[simps, nolint unused_arguments]
def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ₀

lemma hN₁ : κequiv.functor ⋙ preadditive.dold_kan.equivalence.functor =
  (N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi _ _) N₁

lemma hΓ₀ : κequiv'.functor ⋙ preadditive.dold_kan.equivalence.inverse =
    (Γ : chain_complex C ℕ ⥤ _) ⋙ κequiv.functor  :=
functor.congr_obj (functor_extension₂_comp_whiskering_left_to_karoubi _ _) Γ₀

/-- The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`compatibility.lean` to the equivalence `preadditive.dold_kan.equivalence`. -/
def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
compatibility.equivalence (eq_to_iso hN₁) (eq_to_iso hΓ₀)

lemma equivalence_functor : (equivalence : simplicial_object C ≌ _).functor = N := by refl
lemma equivalence_inverse : (equivalence : simplicial_object C ≌ _).inverse = Γ := by refl

/-- The natural isomorphism `NΓ' satisfies the compatibility that is needed
for the construction of our counit isomorphism `η` -/
lemma hη : compatibility.τ₀ =
  compatibility.τ₁ (eq_to_iso hN₁) (eq_to_iso hΓ₀)
  (N₁Γ₀ : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N₁ ≅ κequiv'.functor) :=
begin
  ext K : 3,
  rw compatibility.τ₀_hom_app_eq,
  dsimp [compatibility.τ₁],
  simpa only [id_comp, comp_id, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans,
    N₂Γ₂_to_karoubi_iso_hom] using N₂Γ₂_compatible_with_N₁Γ₀ K,
end

/-- The counit isomorphism induced by `N₁Γ₀_iso` -/
@[simps]
def η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) := compatibility.equivalence_counit_iso
  (N₁Γ₀ : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N₁ ≅ κequiv'.functor)

lemma equivalence_counit_iso :
  dold_kan.equivalence.counit_iso = (η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ)) :=
compatibility.equivalence_counit_iso_eq hη

lemma hε : compatibility.υ (eq_to_iso hN₁) =
  (Γ₂N₁ : κequiv.functor ≅ (N₁ : simplicial_object C ⥤ _) ⋙
  preadditive.dold_kan.equivalence.inverse) :=
begin
  ext1, ext1, ext1, ext1 X,
  erw [nat_trans.comp_app, compatibility_Γ₂N₁_Γ₂N₂_nat_trans],
  dsimp [compatibility.υ],
  simp only [id_comp, comp_id],
  slice_lhs 2 3 { erw [← nat_trans.comp_app, is_iso.hom_inv_id], },
  slice_lhs 2 3 { erw id_comp, },
  simpa only [eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans],
end

/-- The unit isomorphism induced by `Γ₂N₁` -/
@[simps]
def ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ :=
compatibility.equivalence_unit_iso (eq_to_iso hΓ₀) Γ₂N₁

lemma equivalence_unit_iso : dold_kan.equivalence.unit_iso =
  (ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ) :=
compatibility.equivalence_unit_iso_eq hε

end dold_kan

end idempotents

end category_theory
