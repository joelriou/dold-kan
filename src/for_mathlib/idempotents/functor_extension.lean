/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.idempotents.karoubi
import for_mathlib.functor_misc
import category_theory.natural_isomorphism

/-!
# Extension of functors to the idempotent completion

In this file, we obtain an equivalence of categories
`karoubi_universal₁ C D : (C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D)` for
all categories `C` and `D`. The key construction is `functor_extension₁`
which extends a functor `C ⥤ karoubi D` to a functor `karoubi C ⥤ karoubi D`.

TODO : If `D` is idempotent complete, we also have
`karoubi_universal C D : C ⥤ D ≌ karoubi C ⥤ D`.

-/

open category_theory.category
open category_theory.idempotents.karoubi

namespace category_theory

namespace idempotents

variables {C D E : Type*} [category C] [category D] [category E]

lemma nat_trans_eq {F G : karoubi C ⥤ D} (φ : F ⟶ G) (P : karoubi C) :
  φ.app P = F.map (decomp_id_i P) ≫ φ.app P.X ≫ G.map (decomp_id_p P) :=
begin
  rw [← φ.naturality, ← assoc, ← F.map_comp],
  conv { to_lhs, rw [← id_comp (φ.app P), ← F.map_id], },
  congr,
  apply decomp_id,
end

lemma nat_trans_ext {F G : karoubi C ⥤ D} (φ₁ φ₂ : F ⟶ G)
  (h : (𝟙 (to_karoubi C)) ◫ φ₁ = (𝟙 (to_karoubi C)) ◫ φ₂) : φ₁ = φ₂ :=
begin
  ext P,
  rw [nat_trans_eq φ₁, nat_trans_eq φ₂],
  congr' 2,
  have eq := congr_app h P.X,
  simpa only [nat_trans.hcomp_app, nat_trans.id_app, G.map_id, comp_id] using congr_app h P.X,
end

namespace functor_extension₁

@[simps]
def obj (F : C ⥤ karoubi D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).f,
    by simpa only [F.map_comp, hom_ext] using F.congr_map P.idem⟩,
  map := λ P Q f, ⟨(F.map f.f).f,
    by simpa only [F.map_comp, hom_ext] using F.congr_map f.comm⟩, }

@[simps]
def map {F G : C ⥤ karoubi D} (φ : F ⟶ G) : obj F ⟶ obj G :=
{ app := λ P,
  { f := (F.map P.p).f ≫ (φ.app P.X).f,
    comm := begin
      have h := φ.naturality P.p,
      have h' := F.congr_map P.idem,
      simp only [hom_ext, karoubi.comp, F.map_comp] at h h',
      simp only [obj_obj_p, assoc, ← h],
      slice_rhs 1 3 { rw [h', h'], },
    end, },
  naturality' := λ P Q f, begin
    ext,
    dsimp [obj],
    have h := φ.naturality f.f,
    have h' := F.congr_map (comp_p f),
    have h'' := F.congr_map (p_comp f),
    simp only [hom_ext, functor.map_comp, comp] at ⊢ h h' h'',
    slice_rhs 2 3 { rw ← h, },
    slice_lhs 1 2 { rw h', },
    slice_rhs 1 2 { rw h'', },
  end }

end functor_extension₁

variables (C D E)

@[simps]
def functor_extension₁ : (C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D) :=
{ obj := functor_extension₁.obj,
  map := λ F G, functor_extension₁.map,
  map_id' := λ F, by { ext P, exact comp_p (F.map P.p), },
  map_comp' := λ F G H φ φ', begin
    ext P,
    simp only [comp, functor_extension₁.map_app_f, nat_trans.comp_app, assoc],
    have h := φ.naturality P.p,
    have h' := F.congr_map P.idem,
    simp only [hom_ext, comp, F.map_comp] at h h',
    slice_rhs 2 3 { rw ← h, },
    slice_rhs 1 2 { rw h', },
    simp only [assoc],
  end, }

lemma functor_extension₁_comp_whiskering_left_to_karoubi :
  functor_extension₁ C D ⋙
    (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) = 𝟭 _ :=
begin
  refine functor.ext _ _,
  { intro F,
    refine functor.ext _ _,
    { intro X,
      ext,
      { dsimp,
        rw [id_comp, comp_id, F.map_id, id_eq], },
      { refl, }, },
    { intros X Y f,
      ext,
      dsimp,
      simp only [comp_id, eq_to_hom_f, eq_to_hom_refl, comp_p, functor_extension₁.obj_obj_p,
        to_karoubi_obj_p, comp],
      dsimp,
      simp only [functor.map_id, id_eq, p_comp], }, },
  { intros F G φ,
    ext X,
    dsimp,
    simp only [eq_to_hom_app, F.map_id, karoubi.comp, eq_to_hom_f, id_eq, p_comp,
      eq_to_hom_refl, comp_id, comp_p, functor_extension₁.obj_obj_p,
      to_karoubi_obj_p, F.map_id X], },
end

end idempotents

end category_theory
