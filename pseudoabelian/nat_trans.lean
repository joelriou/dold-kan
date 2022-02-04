/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.pseudoabelian.basic

noncomputable theory

open category_theory.category
open category_theory.pseudoabelian.karoubi


namespace category_theory

namespace pseudoabelian

variables {C : Type*} [category C] [preadditive C]

@[simps]
def functor_extension {D : Type*} [category D] [preadditive D]
  (F : C ⥤ D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨F.obj P.X, F.map P.p, 
    by { rw ← F.map_comp, congr, exact P.idempotence, }⟩,
  map := λ P Q f, ⟨F.map f.1,
    by { simp only [← F.map_comp], congr, exact f.2, }⟩, }

@[simps]
def functor_extension' {D : Type*} [category D] [preadditive D]
  (F : C ⥤ karoubi D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).1, begin
    have h := congr_arg (λ (f : P.X ⟶ P.X), F.map f) P.idempotence,
    simpa only [F.map_comp, hom_ext] using h,
  end⟩,
  map := λ P Q f, ⟨(F.map f.1).1, begin
    have h := congr_arg (λ (f : P.X ⟶ Q.X), F.map f) f.2,
    simpa only [F.map_comp, hom_ext] using h,
  end⟩, }

lemma functor_extension_eq {D : Type*} [category D] [preadditive D]
  (F : C ⥤ D) : functor_extension F = functor_extension' (F ⋙ to_karoubi D) :=
begin
  apply functor.ext,
  { intros P Q f,
    ext,
    simpa only [functor_extension'_obj_p, functor_extension'_map_f,
      functor_extension_map_f, functor.comp_map, comp, id_eq,
      functor_extension_obj_p, eq_to_hom_refl, to_karoubi_map_f,
      F.map_comp] using congr_map F f.comm, },
  { intro P,
    ext,
    { simp only [functor_extension'_obj_p, functor.comp_map,
        functor_extension_obj_p, id_comp, eq_to_hom_refl, comp_id,
        to_karoubi_map_f], },
    refl, },
end

@[simps]
def functor_extension'' {D : Type*} [category D] [preadditive D] [is_pseudoabelian D]
  (F : C ⥤ D) : karoubi C ⥤ D :=
  functor_extension F ⋙ (to_karoubi_is_equivalence D).inverse

@[simp]
lemma to_karoubi_comp_functor_extension' {D : Type*} [category D] [preadditive D]
  (F : C ⥤ karoubi D) : to_karoubi C ⋙ functor_extension' F = F :=
begin
  apply functor.ext,
  { intros X Y f,
    ext,
    dsimp,
    simp only [karoubi.comp, karoubi.eq_to_hom_f, eq_to_hom_refl,
      to_karoubi_obj_p, functor_extension'_obj_p, comp_id],
    erw [F.map_id, karoubi.id_eq, ← (F.map f).comm], },
  { intro X,
    ext,
    { dsimp,
      erw F.map_id,
      simp only [id_comp, karoubi.id_eq, comp_id], },
    { refl, }, },
end

@[simp]
lemma to_karoubi_comp_functor_extension {D : Type*} [category D] [preadditive D]
  (F : C ⥤ D) : to_karoubi C ⋙ functor_extension F = F ⋙ to_karoubi D :=
by rw [functor_extension_eq, to_karoubi_comp_functor_extension']

def nat_trans_eq {D : Type*} [category D] {F G : karoubi C ⥤ D} (φ : F ⟶ G) (P : karoubi C) :
  φ.app P = F.map (⟨P.p, by erw [coe_p, comp_id, P.idempotence]⟩ : P ⟶ P.X) ≫ φ.app P.X
    ≫ G.map (⟨P.p, by erw [coe_p, id_comp, P.idempotence]⟩) :=
begin
  rw [← φ.naturality, ← assoc, ← F.map_comp],
  conv { to_lhs, rw [← id_comp (φ.app P), ← F.map_id], },
  congr,
  apply decomp_id,
end

/-
@[simps]
def functor_extension_hom_equiv {D : Type*} [category D] [preadditive D]
  (F G : C ⥤ D) : (F ⟶ G) ≃ (functor_extension F ⟶ functor_extension G) :=
{ to_fun := λ φ,
  { app := λ P,
    { f := F.map P.p ≫ φ.app P.X ≫ G.map P.p,
      comm := begin
        simp only [functor_extension_obj_p],
        slice_rhs 1 2 { rw [← F.map_comp, P.idempotence], },
        slice_rhs 3 4 { rw [← G.map_comp, P.idempotence], },
      end },
    naturality' := λ P Q f, begin
      ext,
      simp only [functor_extension_map_f, comp, assoc, nat_trans.naturality_assoc],
      simp only [← G.map_comp, karoubi.p_comp, ← assoc, karoubi.comp_p],
    end },
  inv_fun := λ ψ,
  { app := λ X, (ψ.app ((to_karoubi C).obj X)).f,
    naturality' := λ X Y f, hom_ext.mp (ψ.naturality ((to_karoubi C).map f)), },
  left_inv := λ φ, begin
    ext X,
    dsimp,
    simp only [functor.map_id, id_comp, comp_id],
  end,
  right_inv := λ ψ, begin
    ext1,
    ext1 P,
    exact (nat_trans_eq ψ P).symm,
  end } 

lemma functor_extension_hom_to_fun_comp {D : Type*} [category D] [preadditive D]
  {F G H : C ⥤ D} (φ : F ⟶ G) (ψ : G ⟶ H) :
  (functor_extension_hom_equiv F H).to_fun (φ ≫ ψ) =
  (functor_extension_hom_equiv F G).to_fun φ ≫ (functor_extension_hom_equiv G H).to_fun ψ :=
begin
  ext P,
  simp only [equiv.to_fun_as_coe, functor_extension_hom_equiv_apply_app_f, comp,
    assoc, nat_trans.naturality_assoc, nat_trans.comp_app, ← H.map_comp, P.idempotence],
end

lemma functor_extension_hom_to_fun_id {D : Type*} [category D] [preadditive D]
  {F : C ⥤ D} :
  (functor_extension_hom_equiv F F).to_fun (𝟙 F) = 𝟙 _ :=
begin
  ext P,
  simp only [equiv.to_fun_as_coe, functor_extension_hom_equiv_apply_app_f, id_eq,
    nat_trans.id_app, functor_extension_obj_p, id_comp, ← F.map_comp, P.idempotence],
end

lemma functor_extension_hom_inv_fun_comp {D : Type*} [category D] [preadditive D]
  {F G H : C ⥤ D} (φ : functor_extension F ⟶ functor_extension G) (ψ : functor_extension G ⟶ functor_extension H) :
  (functor_extension_hom_equiv F H).inv_fun (φ ≫ ψ) =
  (functor_extension_hom_equiv F G).inv_fun φ ≫ (functor_extension_hom_equiv G H).inv_fun ψ :=
begin
  ext X,
  simp only [comp, nat_trans.comp_app, equiv.inv_fun_as_coe,
    functor_extension_hom_equiv_symm_apply_app],
end

lemma functor_extension_hom_inv_fun_id {D : Type*} [category D] [preadditive D]
  {F : C ⥤ D} :
  (functor_extension_hom_equiv F F).inv_fun (𝟙 (functor_extension F)) = 𝟙 _ :=
begin
  ext X,
  simp only [to_karoubi_obj_p, id_eq, nat_trans.id_app, functor_extension_obj_p,
    equiv.inv_fun_as_coe, functor_extension_hom_equiv_symm_apply_app, F.map_id X],
end

@[simps]
def functor_extension_iso_equiv {D : Type*} [category D] [preadditive D]
  (F : C ⥤ D) (G : C ⥤ D) : (F ≅ G) ≃ (functor_extension F ≅ functor_extension G) :=
{ to_fun := λ φ,
  { hom := (functor_extension_hom_equiv F G).to_fun φ.hom,
    inv := (functor_extension_hom_equiv G F).to_fun φ.inv,
    hom_inv_id' := by rw [← functor_extension_hom_to_fun_comp, φ.hom_inv_id, functor_extension_hom_to_fun_id],
    inv_hom_id' := by rw [← functor_extension_hom_to_fun_comp, φ.inv_hom_id, functor_extension_hom_to_fun_id], },
  inv_fun := λ ψ,
  { hom := (functor_extension_hom_equiv F G).inv_fun ψ.hom,
    inv := (functor_extension_hom_equiv G F).inv_fun ψ.inv,
    hom_inv_id' := by rw [← functor_extension_hom_inv_fun_comp, ψ.hom_inv_id, functor_extension_hom_inv_fun_id],
    inv_hom_id' := by rw [← functor_extension_hom_inv_fun_comp, ψ.inv_hom_id, functor_extension_hom_inv_fun_id], },
  left_inv := λ φ, by { ext1, exact (functor_extension_hom_equiv F G).left_inv φ.hom, },
  right_inv := λ ψ, by { ext1, exact (functor_extension_hom_equiv F G).right_inv ψ.hom, }, }
-/

@[simps]
def to_karoubi_hom_equiv {D : Type*} [category D]
  (F G : karoubi C ⥤ D) : (F ⟶ G) ≃ (to_karoubi _ ⋙ F ⟶ to_karoubi _ ⋙ G) :=
{ to_fun := λ φ,
  { app := λ X, φ.app ((to_karoubi C).obj X),
    naturality' := λ X Y f, by simp only [nat_trans.naturality, functor.comp_map], },
  inv_fun := λ ψ,
  { app := λ P, F.map (decomp_id_i P) ≫ (ψ.app P.X) ≫ G.map (decomp_id_p P),
    naturality' := λ P Q f, by {
      slice_lhs 1 2 { rw [← F.map_comp], },
      slice_rhs 3 4 { rw [← G.map_comp], },
      rw [decomp_id_i_naturality, decomp_id_p_naturality,
        F.map_comp, G.map_comp],
      slice_lhs 2 3 { erw ψ.naturality, },
      simp only [assoc],
      refl, }, },
  left_inv := λ φ, by { ext P, exact (nat_trans_eq φ P).symm, },
  right_inv := λ ψ, begin
    ext X,
    dsimp,
    erw [decomp_id_i_to_karoubi, decomp_id_p_to_karoubi,
      F.map_id, G.map_id, comp_id, id_comp],
  end }

lemma to_karoubi_hom_inv_fun_comp {D : Type*} [category D]
  {F G H : karoubi C ⥤ D} (φ : to_karoubi _ ⋙ F ⟶ to_karoubi _ ⋙ G)
  (ψ : to_karoubi _ ⋙ G ⟶ to_karoubi _ ⋙  H) :
  (to_karoubi_hom_equiv F H).inv_fun (φ ≫ ψ) =
  (to_karoubi_hom_equiv F G).inv_fun φ ≫ (to_karoubi_hom_equiv G H).inv_fun ψ :=
begin
  ext P,
  dsimp,
  slice_rhs 3 4 { rw [← G.map_comp, ← decomp_p], },
  erw ψ.naturality P.p,
  slice_rhs 4 5 { erw [← H.map_comp], },
  simp only [assoc],
  congr,
  ext,
  simp only [decomp_id_p_f, comp, to_karoubi_map_f, P.idempotence],
end

lemma to_karoubi_hom_inv_fun_id {D : Type*} [category D]
  {F : karoubi C ⥤ D} :
  (to_karoubi_hom_equiv F F).inv_fun (𝟙 _) = 𝟙 _ :=
begin
  ext P,
  simp only [to_karoubi_hom_equiv_symm_apply_app, nat_trans.id_app, equiv.inv_fun_as_coe],
  erw [id_comp, ← F.map_comp, ← decomp_id, F.map_id],
end

@[simps]
def to_karoubi_iso_equiv {D : Type*} [category D]
  (F G : karoubi C ⥤ D) : (F ≅ G) ≃ (to_karoubi _ ⋙ F ≅ to_karoubi _ ⋙ G) :=
{ to_fun := λ φ,
  { hom := (to_karoubi_hom_equiv F G).to_fun φ.hom,
    inv := (to_karoubi_hom_equiv G F).to_fun φ.inv, },
  inv_fun := λ ψ,
  { hom := (to_karoubi_hom_equiv F G).inv_fun ψ.hom,
    inv := (to_karoubi_hom_equiv G F).inv_fun ψ.inv,
    hom_inv_id' := by rw [← to_karoubi_hom_inv_fun_comp, iso.hom_inv_id, to_karoubi_hom_inv_fun_id],
    inv_hom_id' := by rw [← to_karoubi_hom_inv_fun_comp, iso.inv_hom_id, to_karoubi_hom_inv_fun_id], },
  left_inv := λ φ, by { ext P, simp only [equiv.to_fun_as_coe, equiv.symm_apply_apply,
    equiv.inv_fun_as_coe], },
  right_inv := λ ψ, by { ext X, simp only [equiv.to_fun_as_coe, equiv.apply_symm_apply,
    equiv.inv_fun_as_coe], } }

end pseudoabelian

end category_theory
