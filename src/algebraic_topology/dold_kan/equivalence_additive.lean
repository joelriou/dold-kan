/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.n_comp_gamma

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

variables {C : Type*} [category C] [additive_category C]

namespace category_theory

namespace preadditive

namespace dold_kan

open algebraic_topology.dold_kan

abbreviation N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) := N
abbreviation Γ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) := Γ

@[simps]
def equivalence : karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ) :=
{ functor := N,
  inverse := Γ,
  unit_iso := ΓN.symm,
  counit_iso := NΓ,
  functor_unit_iso_comp' := λ P, begin
    let α := ΓN.app P,
    let β := NΓ.app (N.obj P),
    have hα : N.map (ΓN.symm.hom.app P) = (N.map_iso α).inv := by refl,
    have hβ : NΓ.hom.app (N.obj P) = β.hom := by refl,
    rw [hα, hβ, iso.inv_comp_eq],
    symmetry,
    erw [comp_id, ← comp_id β.hom, ← iso.inv_comp_eq],
    dsimp [α, β],
    exact identity_N_objectwise P,
  end }

end dold_kan

end preadditive

end category_theory
