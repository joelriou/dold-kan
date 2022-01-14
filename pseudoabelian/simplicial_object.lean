/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.pseudoabelian.basic
import algebraic_topology.simplicial_object

noncomputable theory

open category_theory
open category_theory.category
open category_theory.preadditive
open_locale big_operators

variables {C : Type*} [category C] [preadditive C]

@[simps]
instance {X Y : simplicial_object C} : add_comm_group (X ⟶ Y) :=
{ add  := λ f g, { app := f.app + g.app, },
  zero := { app := 0, },
  neg  := λ f, { app := -f.app, },
  add_assoc := λ f g h, by { ext Δ, apply_rules [add_assoc], },
  add_comm    := λ f g, by { ext Δ, apply_rules [add_comm], },
  zero_add      := λ f, by { ext Δ, apply_rules [zero_add], },
  add_zero      := λ f, by { ext Δ, apply_rules [add_zero], },
  add_left_neg  := λ f, by { ext Δ, apply_rules [add_left_neg], }, }

instance : preadditive (simplicial_object C) := { }

namespace category_theory

namespace pseudoabelian

namespace karoubi_simplicial_object_functor

@[simps]
def obj (P : karoubi (simplicial_object C)) : simplicial_object (karoubi C) :=
{ obj := λ Δ, ⟨P.X.obj Δ, P.p.app Δ, congr_app P.idempotence Δ⟩,
  map := λ Δ Δ' θ,
  { f := P.p.app Δ ≫ P.X.map θ,
    comm := begin
      simp only [nat_trans.naturality, assoc],
      have h := congr_app P.idempotence Δ,
      dsimp at h,
      slice_rhs 1 3 { rw [h, h], },
    end, },
  map_id' := λ Δ, by { ext, simp only [P.X.map_id Δ, comp_id, karoubi.id_eq], },
  map_comp' := λ Δ Δ' Δ'' f g, begin
    ext, 
    have h := congr_app P.idempotence Δ,
    dsimp at h,
    simp only [assoc, nat_trans.naturality_assoc, functor.map_comp,
      karoubi.comp],
    slice_rhs 1 2 { rw h, },
    rw [assoc],
  end }

@[simps]
def map {P Q : karoubi (simplicial_object C)} (f : P ⟶ Q) : obj P ⟶ obj Q :=
{ app := λ Δ, ⟨f.f.app Δ, congr_app f.comm Δ⟩,
  naturality' := λ Δ Δ' θ, begin
    ext,
    simp only [karoubi.comp],
    have h := congr_app (karoubi.comp_p f) Δ,
    have h' := congr_app (karoubi.p_comp f) Δ',
    dsimp at h h' ⊢,
    slice_rhs 1 2 { erw h, },
    rw ← P.p.naturality,
    slice_lhs 2 3 { erw h', },
    rw f.f.naturality,
  end }

end karoubi_simplicial_object_functor

variables (C)

@[simps]
def karoubi_simplicial_object : karoubi (simplicial_object C) ⥤ simplicial_object (karoubi C) :=
{ obj := karoubi_simplicial_object_functor.obj,
  map := λ P Q f, karoubi_simplicial_object_functor.map f,
  map_id' := λ P,
    by { ext Δ, simp only [nat_trans.id_app, karoubi.id_eq], dsimp, refl, },
  map_comp' := λ P Q R f f',
    by { ext Δ, simp only [karoubi.comp, nat_trans.comp_app], dsimp, refl, }, }

instance : full (karoubi_simplicial_object C) :=
{ preimage := λ P Q f,
  { f :=
    { app := λ Δ, (f.app Δ).f,
      naturality' := λ Δ Δ' θ, begin
        slice_rhs 1 1 { rw ← karoubi.comp_p, },
        have h := karoubi.hom_ext.mp (f.naturality θ),
        simp only [karoubi.comp] at h,
        dsimp at h ⊢,
        erw [assoc, ← h, ← P.p.naturality θ, assoc, karoubi.p_comp (f.app Δ')],
      end },
    comm := by { ext Δ, exact (f.app Δ).comm, } },
  witness' := λ P Q f, by { ext Δ, dsimp, refl, }, }

instance : faithful (karoubi_simplicial_object C) :=
{ map_injective' := λ P Q f f' h, begin
    ext Δ,
    simp only [karoubi_simplicial_object_functor.map, nat_trans.ext_iff,
      karoubi_simplicial_object_map] at h,
    simpa only using congr_fun h Δ,
  end, }

end pseudoabelian

end category_theory
