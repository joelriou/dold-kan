/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import category_theory.equivalence
import for_mathlib.idempotents.functor_extension

open category_theory
open category_theory.category

noncomputable theory

namespace algebraic_topology

namespace dold_kan

namespace compatibility

variables {A A' B B' : Type*} [category A] [category A'] [category B] [category B']
variables (eA : A ≌ A') (eB : B ≌ B') (e' : A' ≌ B')
variables {F : A ⥤ B'} (hF : eA.functor ⋙ e'.functor ≅ F)
variables {G : B ⥤ A} (hG : eB.functor ⋙ e'.inverse ≅ G ⋙ eA.functor)

def equivalence₀ : A ≌ B' := eA.trans e'

lemma equivalence₀_functor : (equivalence₀ eA e').functor = eA.functor ⋙ e'.functor := by refl
lemma equivalence₀_inverse : (equivalence₀ eA e').inverse = e'.inverse ⋙ eA.inverse := by refl

include hF
variables {eA} {e'}

def equivalence₁ : A ≌ B' :=
begin
  letI : is_equivalence F := is_equivalence_of_iso hF (is_equivalence.of_equivalence (equivalence₀ eA e')),
  exact F.as_equivalence,
end

lemma equivalence₁_functor : (equivalence₁ hF).functor = F := by refl
lemma equivalence₁_inverse : (equivalence₁ hF).inverse = e'.inverse ⋙ eA.inverse := by refl

@[simps]
def equivalence₁_counit_iso :
  (e'.inverse ⋙ eA.inverse) ⋙ F ≅ 𝟭 B' :=
begin
  calc (e'.inverse ⋙ eA.inverse) ⋙ F ≅ (e'.inverse ⋙ eA.inverse) ⋙ (eA.functor ⋙ e'.functor) :
    iso_whisker_left _ hF.symm
  ... ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.functor) ⋙ e'.functor : by refl
  ... ≅ e'.inverse ⋙ 𝟭 _ ⋙ e'.functor : iso_whisker_left _ (iso_whisker_right eA.counit_iso _)
  ... ≅ e'.inverse ⋙ e'.functor : by refl
  ... ≅ 𝟭 B' : e'.counit_iso,
end

lemma equivalence₁_counit_iso_eq : (equivalence₁ hF).counit_iso = equivalence₁_counit_iso hF :=
begin
  ext Y',
  dsimp [equivalence₀, equivalence₁, equivalence₁_counit_iso, nat_iso.hcomp,
    is_equivalence.inverse, is_equivalence.of_equivalence],
  simp only [category_theory.functor.map_id, comp_id, assoc],
end

include eB

def equivalence₂ : A ≌ B := (equivalence₁ hF).trans eB.symm

lemma equivalence₂_functor : (equivalence₂ eB hF).functor = F ⋙ eB.inverse := by refl
lemma equivalence₂_inverse : (equivalence₂ eB hF).inverse = eB.functor ⋙ e'.inverse ⋙ eA.inverse := by refl

@[simps]
def equivalence₂_counit_iso :
  (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ (F ⋙ eB.inverse) ≅ 𝟭 B :=
begin
  calc (eB.functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ (F ⋙ eB.inverse) ≅
    eB.functor ⋙ (e'.inverse ⋙ eA.inverse ⋙ F) ⋙ eB.inverse : by refl
  ... ≅ eB.functor ⋙ 𝟭 _ ⋙ eB.inverse : iso_whisker_left _ (iso_whisker_right (equivalence₁_counit_iso hF) _)
  ... ≅ eB.functor ⋙ eB.inverse : by refl
  ... ≅ 𝟭 B : eB.unit_iso.symm,
end

lemma equivalence₂_counit_iso_eq :
  (equivalence₂ eB hF).counit_iso = equivalence₂_counit_iso eB hF :=
begin
  ext Y',
  dsimp [equivalence₂, equivalence₂_counit_iso],
  erw equivalence₁_counit_iso_eq,
  dsimp [iso.refl],
  erw [nat_trans.id_app, id_comp, comp_id],
end

variable {eB}
include hG

def equivalence : A ≌ B :=
begin
  letI : is_equivalence G := begin
    refine is_equivalence_of_iso _ (is_equivalence.of_equivalence (equivalence₂ eB hF).symm),
    calc eB.functor ⋙ e'.inverse ⋙ eA.inverse ≅ (eB.functor ⋙ e'.inverse) ⋙ eA.inverse : by refl
    ... ≅ (G ⋙ eA.functor) ⋙ eA.inverse : iso_whisker_right hG _
    ... ≅ G ⋙ 𝟭 A : iso_whisker_left _ eA.unit_iso.symm
    ... ≅ G : functor.right_unitor G,
  end,
  exact G.as_equivalence.symm,
end

lemma equivalence_functor : (equivalence hF hG).functor = F ⋙ eB.inverse := by refl
lemma equivalence_inverse : (equivalence hF hG).inverse = G := by refl

def τ₀ : eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor :=
begin
  calc eB.functor ⋙ e'.inverse ⋙ e'.functor
    ≅ eB.functor ⋙ 𝟭 _ : iso_whisker_left _ e'.counit_iso
  ... ≅ eB.functor : functor.right_unitor _,
end

lemma τ₀_hom_app_eq (Y : B) : (τ₀ hF hG).hom.app Y = e'.counit_iso.hom.app (eB.functor.obj Y) :=
by { dsimp [τ₀], erw comp_id, }

def τ₁ (η : G ⋙ F ≅ eB.functor) : eB.functor ⋙ e'.inverse ⋙ e'.functor ≅
  eB.functor :=
begin
  calc eB.functor ⋙ e'.inverse ⋙ e'.functor
    ≅ (eB.functor ⋙ e'.inverse) ⋙ e'.functor : by refl
  ... ≅ (G ⋙ eA.functor) ⋙ e'.functor : iso_whisker_right hG _
  ... ≅ G ⋙ (eA.functor ⋙ e'.functor) : by refl
  ... ≅ G ⋙ F : iso_whisker_left _ hF
  ... ≅ eB.functor : η,
end

variables {η : G ⋙ F ≅ eB.functor} (hη : τ₀ hF hG = τ₁ hF hG η)

include hη
variables {hF} {hG}

def equivalence_counit_iso : G ⋙ (F ⋙ eB.inverse) ≅ 𝟭 B :=
begin
  calc G ⋙ (F ⋙ eB.inverse) ≅ (G ⋙ F) ⋙ eB.inverse : by refl
  ... ≅ eB.functor ⋙ eB.inverse : iso_whisker_right η _ 
  ... ≅ 𝟭 B : eB.unit_iso.symm,
end

lemma equivalence_counit_iso_eq :
  (equivalence hF hG).counit_iso = equivalence_counit_iso hη :=
begin
  ext1, apply nat_trans.ext,
  ext Y,
  dsimp [equivalence, equivalence_counit_iso, equivalence.inverse,
    is_equivalence.inverse, nat_iso.hcomp, is_equivalence.unit_iso, iso.refl, iso.trans],
  simp only [assoc, comp_id, functor.map_comp, id_comp],
  erw [nat_trans.id_app, nat_trans.id_app, (equivalence₂ eB hF).functor.map_id],
  conv { to_lhs, congr, skip, congr, skip, erw id_comp, },
  conv { to_rhs, erw id_comp, },
  suffices h : (equivalence₂ eB hF).functor.map (eA.unit_iso.hom.app (G.obj Y)) ≫
    (equivalence₂ eB hF).functor.map (eA.inverse.map (hG.inv.app Y)) ≫
    (equivalence₂_counit_iso eB hF).hom.app Y =
    eB.inverse.map (η.hom.app Y) ≫ eB.unit_iso.inv.app Y,
  { convert h,
    rw ← equivalence₂_counit_iso_eq eB hF,
    refl, },
  { dsimp [equivalence₂, equivalence₁],
    simp only [equivalence₂_counit_iso_hom_app],
    simp only [← eB.inverse.map_comp, ← assoc],
    congr' 2,
    erw [← τ₀_hom_app_eq hF hG Y, hη],
    dsimp [τ₁],
    erw [id_comp, comp_id],
    conv { to_rhs, erw ← id_comp (η.hom.app Y), },
    simp only [← assoc],
    congr' 1,
    simp only [assoc, nat_trans.naturality, functor.comp_map, equivalence.fun_inv_map, functor.map_comp, nat_trans.naturality_assoc],
    have h := congr_app hF.inv_hom_id (G.obj Y),
    rw [nat_trans.comp_app, nat_trans.id_app] at h,
    conv { to_rhs, erw ← h, congr, skip, erw ← id_comp (hF.hom.app (G.obj Y)), },
    congr' 1,
    simp only [← assoc],
    congr' 1,
    simp only [assoc, ← e'.functor.map_comp],
    conv { to_rhs, erw ← e'.functor.map_id _, },
    congr' 1,
    simp only [iso.inv_hom_id_app_assoc, iso.inv_hom_id_app],
    erw comp_id,
    exact eA.functor_unit_iso_comp (G.obj Y), },
end

end compatibility

end dold_kan

end algebraic_topology
