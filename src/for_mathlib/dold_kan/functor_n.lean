/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.p_infty

/-

# Construction of functors N for the Dold-Kan correspondence

In this file, we construct the functors `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
and `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
for any preadditive category `C`.

In the case `C` is additive, the functor `N₂` shall be the functor of the equivalence
`category_theory.preadditive.dold_kan.equivalence` defined in `equivalence_additive.lean`.

In the case the category `C` is pseudoabelian, the composition of `N₁` with the inverse of the
equivalence `chain_complex C ℕ ⥤ karoubi (chain_complex C ℕ)` will be the functor
`category_theory.idempotents.dold_kan.N` of the equivalence of categories
`category_theory.idempotents.dold_kan.equivalence : simplicial_object C ≌ chain_complex C ℕ`
defined in `equivalence_pseudoabelian.lean`.

(See `equivalence.lean` for the general strategy of proof.)

-/

open category_theory
open category_theory.category
open category_theory.idempotents

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

/-- The functor `simplicial_object C ⥤ karoubi (chain_complex C ℕ)` which maps
`X` to the formal direct factor of `K[X]` defined by `P_infty`. -/
@[simps]
def N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ) :=
{ obj := λ X,
  { X := alternating_face_map_complex.obj X,
    p := P_infty,
    idem := P_infty_idem, },
  map := λ X Y f,
  { f := P_infty ≫ alternating_face_map_complex.map f,
    comm := begin
      ext n,
      simp only [homological_complex.comp_f, alternating_face_map_complex.map,
        chain_complex.of_hom_f],
      slice_rhs 3 4 { erw P_infty_f_naturality, },
      simp only [← assoc, P_infty_f_idem],
    end, },
  map_id' := λ X, begin
    ext n,
    simpa only [homological_complex.comp_f, nat_trans.id_app, karoubi.id_eq,
      alternating_face_map_complex.map, chain_complex.of_hom_f] using comp_id _,
  end,
  map_comp' := λ X Y Z f g, begin
    ext n,
    simp only [karoubi.comp, homological_complex.comp_f, nat_trans.comp_app,
      alternating_face_map_complex.map, chain_complex.of_hom_f],
    slice_rhs 2 3 { erw P_infty_f_naturality, },
    slice_rhs 1 2 { erw P_infty_f_idem, },
    rw assoc,
  end }

/-- The extension of `N₁` to the Karoubi envelope of `simplicial_object C`. -/
@[simps]
def N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) :=
(functor_extension₁ _ _).obj N₁

end dold_kan

end algebraic_topology
