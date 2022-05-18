/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.n_comp_gamma

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents
open algebraic_topology.dold_kan

variables {C : Type*} [category C] [additive_category C]

namespace category_theory

namespace preadditive

namespace dold_kan

@[simps]
def N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) := N₂

@[simps]
def Γ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) := Γ₂

@[simps]
def equivalence : karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ) :=
{ functor := N,
  inverse := Γ,
  unit_iso := Γ₂N₂_iso,
  counit_iso := N₂Γ₂_iso,
  functor_unit_iso_comp' := λ P, begin
    let α := N.map_iso (Γ₂N₂_iso.app P),
    let β := N₂Γ₂_iso.app (N.obj P),
    suffices : α.hom ≫ β.hom = 𝟙 _,
    { exact this, },
    symmetry,
    erw [← iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← iso.inv_comp_eq],
    exact algebraic_topology.dold_kan.identity_N₂_objectwise P,
  end }

end dold_kan

end preadditive

end category_theory
