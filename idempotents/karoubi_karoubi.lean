/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi

/-!
# Idempotence of the Karoubi envelope

In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.

-/

open category_theory
open category_theory.category
open category_theory.idempotents.karoubi

namespace category_theory

namespace idempotents

variables (C : Type*) [category C]

namespace karoubi_karoubi

/-- The canonical functor `karoubi (karoubi C) ⥤ karoubi C` -/
@[simps]
def inverse : karoubi (karoubi C) ⥤ karoubi C :=
  { obj := λ P, ⟨P.X.X, P.p.f,
      by simpa only [hom_ext] using P.idempotence⟩,
    map := λ P Q f, ⟨f.f.f,
      by simpa only [hom_ext] using f.comm⟩, }

instance [preadditive C] : functor.additive (inverse C) := { }

/-- The unit isomorphism of the equivalence -/
@[simps]
def unit_iso : 𝟭 (karoubi C) ≅ to_karoubi (karoubi C) ⋙ inverse C :=
{ hom :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f, begin
      ext,
      simp only [eq_to_hom_f, eq_to_hom_refl, comp_id, functor.id_map, comp, inverse_map_f,
        to_karoubi_map_f, functor.comp_map],
      erw [comp_p, p_comp],
    end },
  inv :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f, begin
      ext,
      simp only [comp, eq_to_hom_f, eq_to_hom_refl, comp_id],
      erw [comp_p f, p_comp f],
    end },
  hom_inv_id' := begin
    ext P,
    simpa only [nat_trans.comp_app, nat_trans.id_app, comp, eq_to_hom_f, eq_to_hom_refl,
      id_eq, comp_id] using P.idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    simpa only [nat_trans.comp_app, nat_trans.id_app, comp, eq_to_hom_f, eq_to_hom_refl,
      id_eq, comp_id] using P.idempotence,
  end, }

/-- The counit isomorphism of the equivalence -/
@[simps]
def counit_iso : inverse C ⋙ to_karoubi (karoubi C) ≅ 𝟭 (karoubi (karoubi C)) :=
{ hom :=
  { app := λ P, ⟨⟨P.p.1, begin
    have h := P.idempotence,
    simp only [hom_ext, comp] at h,
    erw [← assoc, h, comp_p],
    end⟩,
    begin
      have h := P.idempotence,
      simp only [hom_ext, comp] at h ⊢,
      erw [h, h],
    end⟩,
    naturality' := λ P Q f, begin
      have h := comp_p f,
      have h' := p_comp f,
      simp only [hom_ext] at h h' ⊢,
      erw [h, h'],
    end, },
  inv :=
  { app := λ P, ⟨⟨P.p.1, begin
      have h := P.idempotence,
      simp only [hom_ext, comp] at h,
      erw [h, p_comp],
    end⟩,
    begin
      have h := P.idempotence,
      simp only [hom_ext, comp] at h ⊢,
      erw [h, h],
    end⟩,
    naturality' := λ P Q f, begin
      have h := comp_p f,
      have h' := p_comp f,
      simp only [hom_ext] at h h' ⊢,
      erw [h, h'],
    end, },
  hom_inv_id' := begin
    ext P,
    dsimp,
    simpa only [hom_ext, id_eq] using P.idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    dsimp,
    simpa only [hom_ext, id_eq] using P.idempotence,
  end, }

/-- The equivalence `karoubi C ≌ karoubi (karoubi C)` -/
@[simps]
def equivalence : karoubi C ≌ karoubi (karoubi C) :=
{ functor := to_karoubi (karoubi C),
  inverse := karoubi_karoubi.inverse C,
  unit_iso := karoubi_karoubi.unit_iso C,
  counit_iso := karoubi_karoubi.counit_iso C,
  functor_unit_iso_comp' := λ P, begin
    ext,
    simp only [karoubi_karoubi.unit_iso, karoubi_karoubi.counit_iso, eq_to_hom_f,
      eq_to_hom_refl, comp_id, to_karoubi_obj_p, id_eq, assoc, comp,  eq_to_hom_map],
    erw [P.idempotence, P.idempotence],
  end, }

instance additive_functor [preadditive C] : functor.additive (equivalence C).functor :=
  by { dsimp, apply_instance, }

instance additive_inverse [preadditive C] : functor.additive (equivalence C).inverse :=
  by { dsimp, apply_instance, }

end karoubi_karoubi

end idempotents

end category_theory
