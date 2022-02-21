/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import category_theory.equivalence
import for_mathlib.idempotents.functor_extension

open category_theory

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

include eB

def equivalence₂ : A ≌ B := (equivalence₁ hF).trans eB.symm

lemma equivalence₂_functor : (equivalence₂ eB hF).functor = F ⋙ eB.inverse := by refl
lemma equivalence₂_inverse : (equivalence₂ eB hF).inverse = eB.functor ⋙ e'.inverse ⋙ eA.inverse := by refl

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

end compatibility

end dold_kan

end algebraic_topology
