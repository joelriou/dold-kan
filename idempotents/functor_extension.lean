/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi
import category_theory.natural_isomorphism
open category_theory.category
open category_theory.idempotents.karoubi

namespace category_theory
/-
lemma functor.assoc {C D E F : Type*} [category C] [category D]
  [category E] [category F] (φ : C ⥤ D)
  (φ' : D ⥤ E) (φ'' : E ⥤ F) : (φ ⋙ φ') ⋙ φ'' = φ ⋙ (φ' ⋙ φ'') :=
by refl-/

lemma congr_obj {D D' : Type*} [category D] [category D'] {F G : D ⥤ D'}
(h : F = G) : ∀ X : D, F.obj X = G.obj X :=
by { intro X, rw h, }

lemma congr_map {D D' : Type*} [category D] [category D'] (F : D ⥤ D')
{X Y : D} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g :=
by { subst h, }

/-- When a functor `F` is an equivalence of categories, and `G` is isomorphic to `F`, then
`G` is also an equivalence of categories. -/
@[simps]
def is_equivalence_of_iso {C D : Type*} [category C] [category D]
  {F G : C ⥤ D} (e : F ≅ G) (hF : is_equivalence F) : is_equivalence G :=
{ inverse := hF.inverse,
  unit_iso := hF.unit_iso.trans (nat_iso.hcomp e (iso.refl hF.inverse)),
  counit_iso := (nat_iso.hcomp (iso.refl hF.inverse) e.symm).trans hF.counit_iso,
  functor_unit_iso_comp' := λ X, begin
    unfreezingI { rcases hF with ⟨H, η, ε, Fcomp⟩, },
    dsimp [nat_iso.hcomp],
    erw [id_comp, F.map_id, comp_id],
    apply (cancel_epi (e.hom.app X)).mp,
    slice_lhs 1 2 { rw ← e.hom.naturality, },
    slice_lhs 2 3 { rw [← nat_trans.vcomp_app', e.hom_inv_id], },
    simp only [nat_trans.id_app, id_comp, comp_id, F.map_comp, assoc],
    erw ε.hom.naturality,
    slice_lhs 1 2 { rw Fcomp, },
    simp only [functor.id_map, id_comp],
  end }

lemma is_equivalence_of_iso_trans {C D : Type*} [category C] [category D]
  {F G H : C ⥤ D} (e : F ≅ G) (e' : G ≅ H) (hF : is_equivalence F) :
  (is_equivalence_of_iso e' (is_equivalence_of_iso e hF)) =
  is_equivalence_of_iso (e.trans e') hF :=
begin
  unfreezingI { rcases hF with ⟨Finv, Funit, Fcounit, Fcomp⟩, },
  dsimp [is_equivalence_of_iso],
  congr' 1,
  { ext X,
    dsimp [nat_iso.hcomp],
    simp only [id_comp, assoc, functor.map_comp], },
  { ext X,
    dsimp [nat_iso.hcomp],
    simp only [functor.map_id, comp_id, assoc], },
end

lemma is_equivalence_of_iso_refl {C D : Type*} [category C] [category D]
  (F : C ⥤ D) (hF : is_equivalence F) :
  is_equivalence_of_iso (iso.refl F) hF = hF :=
begin
  unfreezingI { rcases hF with ⟨Finv, Funit, Fcounit, Fcomp⟩, },
  dsimp [is_equivalence_of_iso],
  congr' 1,
  { ext X,
    dsimp [nat_iso.hcomp],
    simp only [id_comp, Finv.map_id, comp_id], },
  { ext X,
    dsimp [nat_iso.hcomp],
    simp only [id_comp, F.map_id], }
end

/-- When `F` and `G` are two isomorphic functors, then `F` is an equivalence iff
`G` is. -/
def is_equivalence_equiv_of_iso {C D : Type*} [category C] [category D]
  {F G : C ⥤ D} (e : F ≅ G) : is_equivalence F ≃ is_equivalence G :=
{ to_fun := is_equivalence_of_iso e,
  inv_fun := is_equivalence_of_iso e.symm,
  left_inv := λ hF,
    by rw [is_equivalence_of_iso_trans, iso.self_symm_id, is_equivalence_of_iso_refl],
  right_inv := λ hF,
    by rw [is_equivalence_of_iso_trans, iso.symm_self_id, is_equivalence_of_iso_refl], }

/-- If `G` and `F ⋙ G` are equivalence of categories, then `F` is also an equivalence. -/
def is_equivalence_cancel_comp_right {C D E : Type*} [category C] [category D] [category E]
  (F : C ⥤ D) (G : D ⥤ E) (hG : is_equivalence G) (hGF : is_equivalence (F ⋙ G)) :
  is_equivalence F :=
begin
  let φ : F ⋙ G ⋙ G.inv ≅ F :=
    (nat_iso.hcomp (iso.refl F) hG.unit_iso.symm).trans (eq_to_iso (functor.comp_id F)),
  apply is_equivalence_of_iso ((functor.associator F G G.inv).trans φ),
  exact functor.is_equivalence_trans (F ⋙ G) (G.inv),
end

/-- If `F` and `F ⋙ G` are equivalence of categories, then `G` is also an equivalence. -/
def is_equivalence_cancel_comp_left {C D E : Type*} [category C] [category D] [category E]
  (F : C ⥤ D) (G : D ⥤ E) (hF : is_equivalence F) (hGF : is_equivalence (F ⋙ G)) :
  is_equivalence G :=
begin
  have φ : (F.inv ⋙ F) ⋙ G ≅ G :=
    (nat_iso.hcomp hF.counit_iso (iso.refl G)).trans (eq_to_iso (functor.id_comp G)),
  apply is_equivalence_of_iso ((functor.associator F.inv F G).symm.trans φ),
  exact functor.is_equivalence_trans F.inv (F ⋙ G),
end
#exit
namespace idempotents

variables (C D : Type*) [category C] [category D]

@[simps]
def functor_extension' : (C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D) :=
{ obj := λ F,
  { obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).f,
      by simpa only [F.map_comp, hom_ext]
        using congr_arg (λ (f : P.X ⟶ P.X), F.map f) P.idempotence ⟩,
    map := λ P Q f, ⟨(F.map f.f).f,
      by simpa only [F.map_comp, hom_ext]
        using congr_arg (λ (f : P.X ⟶ Q.X), F.map f) f.comm ⟩, },
  map := λ F G φ,
  { app := λ P,
    { f := (F.map P.p).f ≫ (φ.app P.X).f,
      comm := begin
        dsimp,
        have h := hom_ext.mp (φ.naturality P.p),
        have h' := hom_ext.mp (congr_map F P.idempotence),
        simp only [functor.map_comp, comp] at h h',
        slice_rhs 3 4 { erw ← h },
        slice_rhs 1 3 { erw [h', h'], },
      end, },
    naturality' := λ P Q f, begin
      ext,
      dsimp,
      have h := hom_ext.mp (φ.naturality f.f),
      have h' := hom_ext.mp (congr_map F (comp_p f)),
      have h'' := hom_ext.mp (congr_map F (p_comp f)),
      simp only [functor.map_comp, comp] at ⊢ h h' h'',
      slice_rhs 2 3 { rw ← h, },
      slice_lhs 1 2 { rw h', },
      slice_rhs 1 2 { rw h'', },
    end },
  map_id' := λ F, by { ext P, exact comp_p (F.map P.p), },
  map_comp' := λ F G H φ φ', begin
    ext P,
    dsimp,
    simp only [comp],
    have h := hom_ext.mp (φ.naturality P.p),
    simp only [comp] at h,
    slice_rhs 2 3 { rw ← h, },
    conv { to_lhs, congr, rw ← P.idempotence, },
    simp only [functor.map_comp, comp, assoc],
  end, }

lemma functor_extension'_comp_whiskering_left_to_karoubi :
  functor_extension' C D ⋙ (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) = 𝟭 _ :=
begin
  apply functor.ext,
  { intros F G φ,
    ext X,
    dsimp,
    simp only [functor.map_id, id_eq, eq_to_hom_f, eq_to_hom_refl, comp_id,
      functor_extension'_obj_obj_p, to_karoubi_obj_p, eq_to_hom_app, comp],
    rw [F.map_id X, id_eq, comp_p (φ.app X)], },
  { intro F,
    apply functor.ext,
    { intros X Y f,
      ext,
      dsimp,
      simp only [eq_to_hom_f, eq_to_hom_refl, comp_id, functor_extension'_obj_obj_p,
        to_karoubi_obj_p, comp],
      erw [F.map_id, id_eq],
      exact (F.map f).comm, },
    { intro X,
      ext,
      { dsimp,
        rw [id_comp, comp_id, F.map_id, id_eq], },
      { refl, }, }, }
end

@[simps]
def functor_extension'_counit_iso :
(whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) ⋙ functor_extension' C D ≅ 𝟭 _ :=
{ hom :=
  { app := λ G,
    { app := λ P,
      { f := (G.map (decomp_id_p P)).f,
        comm := begin
          have eq : P.decomp_id_p = (to_karoubi C).map P.p ≫ P.decomp_id_p ≫ 𝟙 _,
          { simp only [P.idempotence, decomp_id_p_f, to_karoubi_map_f, id_eq, comp, hom_ext], },
          have eq' := hom_ext.mp (congr_map G eq),
          simp only [G.map_comp, G.map_id] at eq',
          simpa only [comp] using eq',
        end },
      naturality' := λ P Q f, begin
        ext,
        simpa only [G.map_comp, hom_ext] using (congr_map G (decomp_id_p_naturality f)).symm,
      end },
    naturality' := λ G G' φ, begin
      ext P,
      have eq := hom_ext.mp (φ.naturality P.decomp_id_p),
      have eq' : ((to_karoubi C).map P.p) ≫ P.decomp_id_p = P.decomp_id_p,
      { ext, simpa only using P.idempotence, },
      simp only [comp] at eq,
      simp only [functor_extension'_map_app_f, whisker_left_app, assoc, functor.comp_map,
        whiskering_left_obj_map, nat_trans.comp_app, comp, functor.id_map],
      erw [← eq, ← assoc],
      dsimp,
      congr' 1,
      simpa only [G.map_comp] using hom_ext.mp (congr_map G eq'),
    end },
  inv :=
  { app := λ G,
    { app := λ P,
      { f := (G.map (decomp_id_i P)).f,
        comm := begin
          have eq : P.decomp_id_i = 𝟙 _ ≫ P.decomp_id_i ≫ (to_karoubi C).map P.p,
          { simp only [P.idempotence, decomp_id_i_f, to_karoubi_map_f, id_eq, comp, hom_ext], },
          have eq' := hom_ext.mp (congr_map G eq),
          simp only [G.map_comp, G.map_id] at eq',
          simpa only [comp] using eq',
        end, },
      naturality' := λ P Q f, begin
        ext,
        simpa only [G.map_comp, hom_ext] using congr_map G (decomp_id_i_naturality f),
      end },
    naturality' := λ G G' φ, begin
      ext P,
      have eq := hom_ext.mp (φ.naturality P.decomp_id_i),
      have eq' : P.decomp_id_i = P.decomp_id_i ≫ ((to_karoubi C).map P.p),
      { ext, simpa only using P.idempotence.symm, },
      simp only [comp] at eq,
      simp only [functor.id_map, nat_trans.comp_app, comp, functor_extension'_map_app_f,
        whisker_left_app, functor.comp_map, whiskering_left_obj_map, ← eq],
      rw ← assoc,
      congr' 1,
      simpa only [G.map_comp] using hom_ext.mp (congr_map G eq'),
    end },
  hom_inv_id' := begin
    ext G P,
    simpa only [G.map_comp, G.map_id] using hom_ext.mp (congr_map G P.decomp_p.symm),
  end,
  inv_hom_id' := begin
    ext G P,
    simpa only [G.map_comp, G.map_id] using hom_ext.mp (congr_map G P.decomp_id.symm),
  end, }

@[simps]
def karoubi_universal' : (C ⥤ karoubi D) ≌ (karoubi C ⥤ karoubi D) :=
{ functor := functor_extension' C D,
  inverse := (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C),
  unit_iso := eq_to_iso (functor_extension'_comp_whiskering_left_to_karoubi C D).symm,
  counit_iso := (functor_extension'_counit_iso C D),
  functor_unit_iso_comp' := λ F, begin
    ext P,
    simpa only [eq_to_iso.hom, eq_to_hom_app, eq_to_hom_map, eq_to_hom_refl, id_comp]
      using congr_map F P.idempotence,
  end, }

@[simps]
def functor_extension'' : (C ⥤ D) ⥤ (karoubi C ⥤ karoubi D) :=
(whiskering_right C D (karoubi D)).obj (to_karoubi D) ⋙ functor_extension' C D

lemma functor_extension''_comp_whiskering_left_to_karoubi :
  functor_extension'' C D ⋙
    (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) =
  (whiskering_right C D (karoubi D)).obj (to_karoubi D) :=
by simp only [functor_extension'', functor.assoc,
  functor_extension'_comp_whiskering_left_to_karoubi, functor.comp_id]

section

variable [is_idempotent_complete D]

noncomputable instance : is_equivalence (to_karoubi D) :=
to_karoubi_is_equivalence D

@[simps]
noncomputable def karoubi_universal'' : (C ⥤ D) ≌
  (karoubi C ⥤ karoubi D) :=
(equivalence.congr_right (to_karoubi D).as_equivalence).trans
    (karoubi_universal' C D)

lemma karoubi_universal''_functor_eq :
  (karoubi_universal'' C D).functor = functor_extension'' C D := rfl

noncomputable instance : is_equivalence (functor_extension'' C D) :=
by { rw ← karoubi_universal''_functor_eq, apply_instance, }

@[simps]
noncomputable def functor_extension :
  (C ⥤ D) ⥤ (karoubi C ⥤ D) :=
functor_extension'' C D ⋙ (whiskering_right (karoubi C) (karoubi D) D).obj
    (to_karoubi_is_equivalence D).inverse

@[simps]
noncomputable def karoubi_universal : (C ⥤ D) ≌ (karoubi C ⥤ D) :=
(karoubi_universal'' C D).trans (equivalence.congr_right (to_karoubi D).as_equivalence.symm)

lemma karoubi_universal_functor_eq :
  (karoubi_universal C D).functor = functor_extension C D := rfl

noncomputable instance : is_equivalence (functor_extension C D) :=
by { rw ← karoubi_universal_functor_eq, apply_instance, }

noncomputable instance : is_equivalence ((whiskering_left C (karoubi C) D).obj (to_karoubi C)) :=
begin
  let F₁ := ((whiskering_left C (karoubi C) D).obj (to_karoubi C)),
  let F₂ := ((whiskering_right C _ _).obj (to_karoubi D) ⋙
    (whiskering_right C _ _).obj (to_karoubi D).inv),
  apply is_equivalence_cancel_comp_right F₁ F₂,
  { exact is_equivalence.of_equivalence
      (@equivalence.congr_right _ _ _ _ C _
      ((to_karoubi D).as_equivalence.trans (to_karoubi D).as_equivalence.symm)), },
  { rw [show F₁ ⋙ F₂ = (karoubi_universal C D).inverse, by refl],
    apply_instance, }
end

end section

#exit

variables {C} {D}
lemma nat_trans_eq {F G : karoubi C ⥤ D} (φ : F ⟶ G) (P : karoubi C) :
  φ.app P = F.map (decomp_id_i P) ≫ φ.app P.X ≫ G.map (decomp_id_p P) :=
begin
  rw [← φ.naturality, ← assoc, ← F.map_comp],
  conv { to_lhs, rw [← id_comp (φ.app P), ← F.map_id], },
  congr,
  apply decomp_id,
end

lemma nat_trans_eq' {F G : karoubi C ⥤ D} (φ : F ⟶ G) (P : karoubi C) :
  φ.app P = F.map (decomp_id_i P) ≫ φ.app ((to_karoubi C).obj P.X) ≫ G.map (decomp_id_p P) :=
by { rw [nat_trans_eq], refl, }

#exit

instance : is_equivalence (functor_extension C D) :=
by { rw ← karoubi_universal'_functor, apply_instance, }

instance [is_idempotent_complete D] :
  is_equivalence ((whiskering_left C (karoubi C) D).obj (to_karoubi C)) := sorry


variables (C) (D)





end idempotents

end category_theory
#lint
