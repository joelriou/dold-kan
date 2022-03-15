/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.p_infty

open category_theory
open category_theory.category
open category_theory.idempotents

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

@[simps]
def N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ) :=
{ obj := λ X,
  { X := alternating_face_map_complex.obj X,
    p := P_infty,
    idem := P_infty_is_a_projection, },
  map := λ X Y f,
  { f := P_infty ≫ alternating_face_map_complex.map f,
    comm := begin
      ext n,
      simp only [homological_complex.comp_f, alternating_face_map_complex.map,
        chain_complex.of_hom_f],
      slice_rhs 3 4 { erw P_infty_degreewise_naturality, },
      simp only [← assoc, P_infty_degreewise_is_a_projection],
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
    slice_rhs 2 3 { erw P_infty_degreewise_naturality, },
    slice_rhs 1 2 { erw P_infty_degreewise_is_a_projection, },
    rw assoc,
  end }

@[simps]
def N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) :=
(functor_extension' _ _).obj N₁

end dold_kan

end algebraic_topology
