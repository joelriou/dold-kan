/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.functor_extension
import for_mathlib.functor_misc

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

variables (C D E : Type*) [category C] [category D] [category E]

namespace karoubi_universal₁

@[simps]
def counit_iso :
  (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) ⋙
    functor_extension₁ C D ≅ 𝟭 _ :=
nat_iso.of_components (λ G,
{ hom :=
  { app := λ P,
    { f := (G.map (decomp_id_p P)).f,
      comm := begin
        have eq : P.decomp_id_p = (to_karoubi C).map P.p ≫ P.decomp_id_p ≫ 𝟙 _,
        { simp only [P.idem, decomp_id_p_f, to_karoubi_map_f, id_eq, comp, hom_ext], },
        simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map eq,
      end },
      naturality' := λ P Q f, begin
        ext,
        simpa only [hom_ext, G.map_comp] using (G.congr_map (decomp_id_p_naturality f)).symm,
      end },
  inv :=
  { app := λ P,
    { f := (G.map (decomp_id_i P)).f,
      comm := begin
        have eq : P.decomp_id_i = 𝟙 _ ≫ P.decomp_id_i ≫ (to_karoubi C).map P.p,
        { simp only [P.idem, decomp_id_i_f, to_karoubi_map_f, id_eq, comp, hom_ext], },
        simpa only [hom_ext, G.map_comp, G.map_id] using (G.congr_map eq),
      end, },
    naturality' := λ P Q f, begin
      ext,
      simpa only [hom_ext, G.map_comp] using G.congr_map (decomp_id_i_naturality f),
    end },
  hom_inv_id' := begin
    ext P,
    simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map P.decomp_p.symm,
  end,
  inv_hom_id' := begin
    ext P,
    simpa only [hom_ext, G.map_comp, G.map_id] using G.congr_map P.decomp_id.symm,
  end, })
begin
  intros G G' φ,
  ext P,
  dsimp,
  simp only [nat_trans_eq φ P, comp, functor_extension₁.map_app_f,
    functor.comp_map, whisker_left_app],
  rw [P.decomp_p, G.map_comp, comp, assoc, assoc],
  refl,
end

end karoubi_universal₁

@[simps]
def karoubi_universal₁ : (C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D) :=
{ functor := functor_extension₁ C D,
  inverse := (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C),
  unit_iso := eq_to_iso (functor_extension₁_comp_whiskering_left_to_karoubi C D).symm,
  counit_iso := karoubi_universal₁.counit_iso C D,
  functor_unit_iso_comp' := λ F, begin
    ext P,
    simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_refl, id_comp]
      using F.congr_map P.idem,
  end, }

lemma functor_extension₁_comp
  (F : C ⥤ karoubi D) (G : D ⥤ karoubi E) :
  (functor_extension₁ C E).obj (F ⋙ (functor_extension₁ D E).obj G) =
  (functor_extension₁ C D).obj F ⋙ (functor_extension₁ D E).obj G :=
begin
  apply functor.ext,
  { intros X Y f,
    erw [id_comp, comp_id],
    refl, },
  { intro P,
    ext,
    { dsimp,
      erw [comp_id, id_comp], },
    { refl, }, }
end

@[simps]
def functor_extension₂ : (C ⥤ D) ⥤ (karoubi C ⥤ karoubi D) :=
(whiskering_right C D (karoubi D)).obj (to_karoubi D) ⋙ functor_extension₁ C D

lemma functor_extension₂_comp_whiskering_left_to_karoubi :
  functor_extension₂ C D ⋙
    (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) =
  (whiskering_right C D (karoubi D)).obj (to_karoubi D) :=
by simp only [functor_extension₂, functor.assoc_eq,
  functor_extension₁_comp_whiskering_left_to_karoubi, functor.comp_id]

section is_idempotent_complete

variable [is_idempotent_complete D]

noncomputable instance : is_equivalence (to_karoubi D) := to_karoubi_is_equivalence D

@[simps]
noncomputable def karoubi_universal₂ : (C ⥤ D) ≌
  (karoubi C ⥤ karoubi D) :=
(equivalence.congr_right (to_karoubi D).as_equivalence).trans
    (karoubi_universal₁ C D)

lemma karoubi_universal₂_functor_eq :
  (karoubi_universal₂ C D).functor = functor_extension₂ C D := rfl

noncomputable instance : is_equivalence (functor_extension₂ C D) :=
by { rw ← karoubi_universal₂_functor_eq, apply_instance, }

@[simps]
noncomputable def functor_extension :
  (C ⥤ D) ⥤ (karoubi C ⥤ D) :=
functor_extension₂ C D ⋙ (whiskering_right (karoubi C) (karoubi D) D).obj
    (to_karoubi_is_equivalence D).inverse

@[simps]
noncomputable def karoubi_universal : (C ⥤ D) ≌ (karoubi C ⥤ D) :=
(karoubi_universal₂ C D).trans (equivalence.congr_right (to_karoubi D).as_equivalence.symm)

lemma karoubi_universal_functor_eq :
  (karoubi_universal C D).functor = functor_extension C D := rfl

noncomputable instance : is_equivalence (functor_extension C D) :=
by { rw ← karoubi_universal_functor_eq, apply_instance, }

noncomputable instance : is_equivalence ((whiskering_left C (karoubi C) D).obj (to_karoubi C)) :=
begin
  let F₁ := ((whiskering_left C (karoubi C) D).obj (to_karoubi C)),
  let F₂ := ((whiskering_right C _ _).obj (to_karoubi D) ⋙
    (whiskering_right C _ _).obj (to_karoubi D).inv),
  apply is_equivalence.cancel_comp_right F₁ F₂,
  { exact is_equivalence.of_equivalence
      (@equivalence.congr_right _ _ _ _ C _
      ((to_karoubi D).as_equivalence.trans (to_karoubi D).as_equivalence.symm)), },
  { rw [show F₁ ⋙ F₂ = (karoubi_universal C D).inverse, by refl],
    apply_instance, }
end

end is_idempotent_complete

end idempotents

end category_theory
