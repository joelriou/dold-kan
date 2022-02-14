/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.p_infty
import for_mathlib.idempotents.functor_extension

open category_theory
open category_theory.category
open category_theory.idempotents

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

namespace N'_functor

@[simps]
def obj (X : simplicial_object C) : karoubi (chain_complex C ℕ) :=
  ⟨(alternating_face_map_complex C).obj X, P_infty, P_infty_is_a_projector⟩

@[simps]
def map {X Y : simplicial_object C} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ⟨P_infty ≫ (alternating_face_map_complex C).map f,
begin
  ext n,
  dsimp [P_infty],
  conv { to_lhs, congr, rw [← P_is_a_projector, homological_complex.comp_f], },
  slice_lhs 2 3 { rw ← P_degreewise_naturality, },
  slice_rhs 1 2 { rw [← homological_complex.comp_f,
    P_is_a_projector], },
  rw assoc,
end⟩

end N'_functor

@[simps]
def N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ) :=
{ obj := N'_functor.obj,
  map := λ X Y f, N'_functor.map f,
  map_id' := λ X, begin
    ext n,
    simp only [homological_complex.comp_f, chain_complex.of_hom_f,
      nat_trans.id_app, alternating_face_map_complex_map,
      alternating_face_map_complex.map, karoubi.id_eq, N'_functor.map_f, N'_functor.obj_p],
    erw comp_id,
  end,
  map_comp' := λ X Y Z f g, begin
    ext n,
    simp only [homological_complex.comp_f, karoubi.comp,
      alternating_face_map_complex.map, alternating_face_map_complex_map,
      chain_complex.of_hom_f, nat_trans.comp_app, P_infty, N'_functor.map_f],
      slice_rhs 2 3 { erw P_degreewise_naturality, },
      slice_rhs 1 2 { rw [← homological_complex.comp_f,
        P_is_a_projector], },
      rw assoc,
  end }

@[simps]
def N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ) :=
(functor_extension' _ _).obj N'

end dold_kan

end algebraic_topology
