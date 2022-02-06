/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi

open category_theory.category
open category_theory.idempotents.karoubi

namespace category_theory

lemma congr_obj {D D' : Type*} [category D] [category D'] {F G : D ⥤ D'}
(h : F = G) : ∀ X : D, F.obj X = G.obj X :=
by { intro X, rw h, }

lemma congr_map {D D' : Type*} [category D] [category D'] (F : D ⥤ D')
{X Y : D} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g :=
by { subst h, }

namespace idempotents

variables (C D : Type*) [category C] [category D]

@[simps]
def functor_extension : (C ⥤ karoubi D) ⥤ (karoubi C ⥤ karoubi D) :=
{ obj := λ F,
  { obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).f, begin
      have h := congr_arg (λ (f : P.X ⟶ P.X), F.map f) P.idempotence,
      simpa only [F.map_comp, hom_ext] using h,
    end⟩,
    map := λ P Q f, ⟨(F.map f.f).f, begin
      have h := congr_arg (λ (f : P.X ⟶ Q.X), F.map f) f.comm,
      simpa only [F.map_comp, hom_ext] using h,
    end⟩, },
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

lemma functor_extension_comp_whiskering_left_to_karoubi :
  functor_extension C D ⋙ (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) = 𝟭 _ :=
begin
  apply functor.ext,
  { intros F G φ,
    ext X,
    dsimp,
    simp only [functor.map_id, id_eq, eq_to_hom_f, eq_to_hom_refl, comp_id,
      functor_extension_obj_obj_p, to_karoubi_obj_p, eq_to_hom_app, comp],
    rw [F.map_id X, id_eq, comp_p (φ.app X)], },
  { intro F,
    apply functor.ext,
    { intros X Y f,
      ext,
      dsimp,
      simp only [eq_to_hom_f, eq_to_hom_refl, comp_id, functor_extension_obj_obj_p,
        to_karoubi_obj_p, comp],
      erw [F.map_id, id_eq],
      exact (F.map f).comm, },
    { intro X,
      ext,
      { dsimp,
        rw [id_comp, comp_id, F.map_id, id_eq], },
      { refl, }, }, }
end

instance : faithful (functor_extension C D) := ⟨λ F G φ₁ φ₂, begin
  intro h,
  ext X,
  have h' := hom_ext.mp (congr_app h (((to_karoubi C).obj X))),
  dsimp at h',
  simpa only [functor.map_id, id_eq, p_comp] using h',
end⟩

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

instance : full (functor_extension C D) :=
{ preimage := λ F G ψ, begin
    let φ' := functor.map ((whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C)) ψ,
    have eq : ∀ (H : C ⥤ karoubi D), _ = H :=
      congr_obj (functor_extension_comp_whiskering_left_to_karoubi C D),
    exact eq_to_hom (eq F).symm ≫ φ' ≫ eq_to_hom (eq G),
  end,
  witness' := λ F G ψ, begin
    ext P,
    dsimp,
    simp only [eq_to_hom_f, functor_extension_obj_obj_p, to_karoubi_obj_p, eq_to_hom_refl,
      comp_id, eq_to_hom_app, comp, nat_trans_eq' ψ P, G.map_id P.X, id_eq],
    dsimp,
    have h := p_comp (ψ.app ((to_karoubi C).obj P.X)),
    have h' := ψ.naturality ((to_karoubi C).map P.p),
    have h'' := comp_p (G.map P.p),
    have h''' := congr_map G P.idempotence,
    dsimp at h,
    simp only [functor.map_id, id_eq, functor_extension_obj_map_f, to_karoubi_map_f, comp,
      hom_ext, functor.map_comp] at h h' h'' h''',
    slice_lhs 2 3 { erw h, },
    slice_lhs 1 2 { erw h', },
    slice_lhs 2 3 { erw h'', },
    slice_rhs 1 2 { erw h', },
    slice_rhs 2 3 { erw h''', },
  end }

variables (C) (D)

@[simps]
def functor_extension' : (C ⥤ D) ⥤ (karoubi C ⥤ karoubi D) :=
(whiskering_right C D (karoubi D)).obj (to_karoubi D) ⋙ functor_extension C D

lemma functor.assoc {E F : Type*} [category E] [category F] (φ : C ⥤ D)
  (φ' : D ⥤ E) (φ'' : E ⥤ F) : (φ ⋙ φ') ⋙ φ'' = φ ⋙ (φ' ⋙ φ'') :=
by refl

lemma functor_extension'_comp_whiskering_left_to_karoubi :
  functor_extension' C D ⋙
    (whiskering_left C (karoubi C) (karoubi D)).obj (to_karoubi C) =
  (whiskering_right C D (karoubi D)).obj (to_karoubi D) :=
by simp only [functor_extension', functor.assoc,
  functor_extension_comp_whiskering_left_to_karoubi, functor.comp_id]

noncomputable def functor_extension'' [is_idempotent_complete D] :
  (C ⥤ D) ⥤ (karoubi C ⥤ D) :=
functor_extension' C D ⋙ (whiskering_right (karoubi C) (karoubi D) D).obj
    (to_karoubi_is_equivalence D).inverse

end idempotents

end category_theory
