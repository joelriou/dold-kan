/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.pseudoabelian.basic

open category_theory
open category_theory.category
open category_theory.pseudoabelian.karoubi

namespace category_theory

namespace pseudoabelian

variables (C : Type*) [category C] [preadditive C]

namespace karoubi_karoubi

@[simps]
def inverse : karoubi (karoubi C) ⥤ karoubi C :=
  { obj := λ P, ⟨P.X.X, P.p.1,
      by simpa only [karoubi.hom_ext] using P.idempotence⟩,
    map := λ P Q f, ⟨f.1.1,
      by simpa only [hom_ext] using f.2⟩, }

instance : functor.additive (inverse C) := { }

@[simps]
def unit_iso : 𝟭 (karoubi C) ≅ to_karoubi (karoubi C) ⋙ inverse C :=
{ hom :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f,
      by { cases P, cases Q, cases f, dsimp [inverse],
        simp only [comp_id, id_comp, hom_ext], }, },
  inv :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f, begin
      cases P,
      cases Q,
      dsimp [inverse],
      simp only [comp_id, id_comp, hom_ext],
    end },
  hom_inv_id' := begin
    ext P,
    cases P,
    dsimp,
    simpa only [id_eq, hom_ext] using P_idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    cases P,
    dsimp,
    simpa only [id_eq, hom_ext] using P_idempotence,
  end, }

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

@[simps]
def equivalence : karoubi C ≌ karoubi (karoubi C) :=
{ functor := to_karoubi (karoubi C),
  inverse := karoubi_karoubi.inverse C,
  unit_iso := karoubi_karoubi.unit_iso C,
  counit_iso := karoubi_karoubi.counit_iso C,
  functor_unit_iso_comp' := λ P, begin
    cases P,
    dsimp [karoubi_karoubi.unit_iso, karoubi_karoubi.counit_iso, to_karoubi],
    simp only [comp, id_eq, subtype.coe_mk, P_idempotence],
  end, }

instance additive_functor : functor.additive (equivalence C).functor :=
  by { dsimp, apply_instance, }

instance additive_inverse : functor.additive (equivalence C).inverse :=
  by { dsimp, apply_instance, }

end karoubi_karoubi

end pseudoabelian

end category_theory

