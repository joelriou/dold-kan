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
    have h := congr_app identity_N P,
    simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app,
      (Γ ⋙ N).map_id, comp_id] at h,
    erw [id_comp] at h,
    rw [← is_iso.inv_id],
    simp only [← h, is_iso.inv_comp],
    congr',
    { rw ← functor.map_inv,
      congr,
      simpa only [← comp_hom_eq_id, nat_trans.comp_app] using congr_app ΓN.inv_hom_id P, },
    { simpa only [← comp_hom_eq_id, nat_trans.comp_app] using congr_app NΓ.hom_inv_id (N.obj P), },
  end }

end dold_kan

end preadditive

end category_theory
