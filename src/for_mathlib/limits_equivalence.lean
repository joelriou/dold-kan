/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.creates
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.zero
import category_theory.preadditive.additive_functor
import for_mathlib.functor_misc

open category_theory
open category_theory.category
open category_theory.limits

noncomputable theory
open classical

universes w' w v₁ v₂ u₁ u₂
namespace category_theory

namespace pseudoabelian

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

def preserves_limit_of_equivalence {J : Type w} [category.{w'} J] (K : J ⥤ C) (e : C ≌ D) :
  limits.preserves_limit K e.functor := ⟨λ c hc,
{ lift := λ s, e.counit_iso.inv.app s.X ≫
    e.functor.map (hc.lift ((limits.cones.functoriality_equivalence K e).inverse.obj s)),
  fac' := λ s j, begin
    erw [assoc, ← e.functor.map_comp,
      congr_map e.functor (hc.fac' ((limits.cones.functoriality_equivalence K e).inverse.obj s) j)],
    dsimp,
    simp only [equivalence.counit_inv_functor_comp, equivalence.fun_inv_map, assoc,
      id_comp, iso.inv_hom_id_app_assoc, comp_id, functor.map_comp],
  end,
  uniq' := λ s m hm, begin 
    have h := hc.uniq' ((limits.cones.functoriality_equivalence K e).inverse.obj s)
      (e.inverse.map m ≫ e.unit_iso.inv.app c.X) _, swap,
    { intro j,
      dsimp,
      erw [← congr_map e.inverse (hm j), id_comp, comp_id, functor.map_comp,
        equivalence.inv_fun_map, assoc, assoc, assoc, assoc,
        iso.hom_inv_id_app, comp_id], },
    rw ← congr_map e.functor h,
    erw [functor.map_comp, equivalence.fun_inv_map, assoc, assoc,
      equivalence.counit_inv_functor_comp, iso.inv_hom_id_app_assoc, comp_id],
  end } ⟩

def has_limit_of_equivalence {J : Type w} [category.{w'} J] (e : C ≌ D) (K : J ⥤ C)
  (hK : limits.has_limit K) : limits.has_limit (K ⋙ e.functor) :=
⟨nonempty.intro
  { cone := e.functor.map_cone (limits.limit.cone K),
    is_limit := begin
      apply (preserves_limit_of_equivalence K e).preserves,
      exact limits.limit.is_limit K,
    end }⟩

def has_limit_iff_of_equivalence {J : Type w} [category.{w'} J] (e : C ≌ D) (K : J ⥤ C) :
  limits.has_limit K ↔ limits.has_limit (K ⋙ e.functor) :=
begin
  split,
  { apply has_limit_of_equivalence, },
  { intro h,
    haveI h' := has_limit_of_equivalence e.symm (K ⋙ e.functor) h,
    let isom : (K ⋙ e.functor) ⋙ e.symm.functor ≅ K :=
    { hom := (𝟙 K ◫ e.unit_iso.inv : K ⋙ e.functor ⋙ e.inverse ⟶ _) ≫ (eq_to_hom (functor.comp_id K)),
      inv := (eq_to_hom (functor.comp_id K).symm) ≫ (𝟙 K ◫ e.unit_iso.hom),
      hom_inv_id' := begin
        ext j,
        simpa only [functor.id_map, functor.comp_map, nat_trans.hcomp_app, functor.map_id, 
          nat_trans.id_app, assoc, id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc,
          nat_trans.comp_app, comp_id, iso.inv_hom_id_app],
      end,
      inv_hom_id' := begin
        ext j,
        simpa only [functor.id_map, functor.comp_map, nat_trans.hcomp_app, eq_to_hom_app, functor.map_id,
          nat_trans.id_app, assoc, id_comp, eq_to_hom_refl, comp_id, nat_trans.comp_app,
          iso.hom_inv_id_app],
      end },
    exact limits.has_limit_of_iso isom, },
end

open limits.walking_parallel_pair
open limits.walking_parallel_pair_hom

def walking_parallel_pair_change_universes_functor :
  walking_parallel_pair.{v₁} ⥤ walking_parallel_pair.{v₂} :=
{ obj := λ x, by { cases x, exacts [zero, one], },
  map := λ i j f, by { cases f, exacts [left, right, 𝟙 _], },
  map_comp' := by { rintros (_|_) (_|_) (_|_) (_|_|_) (_|_|_); refl, }, }

def walking_parallel_pair_change_universes_equivalence :
  walking_parallel_pair.{v₁} ≌ walking_parallel_pair.{v₂} :=
{ functor := walking_parallel_pair_change_universes_functor,
  inverse := walking_parallel_pair_change_universes_functor,
  unit_iso := begin
    apply eq_to_iso,
    apply functor.ext,
    { intros i j f, cases f, tidy, },
    { rintros (_|_);refl, }
  end,
  counit_iso := begin
    apply eq_to_iso,
    apply functor.ext,
    { intros i j f, cases f, tidy, },
    { rintros (_|_); refl, }
  end, }

lemma has_equalizer_of_equivalence (e : C ≌ D) {X Y : C} (f g : X ⟶ Y)
  (hfg : has_equalizer f g) :
  has_equalizer (e.functor.map f) (e.functor.map g) :=
begin
  let F := walking_parallel_pair_change_universes_equivalence.{v₁ v₂},
  apply category_theory.limits.has_limit_of_equivalence_comp F,
  let φ := parallel_pair f g,
  have eq : φ ⋙ e.functor = F.functor ⋙
    parallel_pair (e.functor.map f) (e.functor.map g),
  { apply functor.ext,
    { intros i j f, cases f, tidy, },
    { intro i, cases i, tidy, }, },
  rw ← eq,
  exact (has_limit_iff_of_equivalence e φ).mp hfg,
end

lemma has_kernel_of_equivalence [preadditive C] [preadditive D]
  (e : C ≌ D) [functor.additive e.functor] {X Y : C} (f : X ⟶ Y)
  (hf : has_kernel f) : has_kernel (e.functor.map f) :=
begin
  have h : functor.preserves_zero_morphisms e.functor := infer_instance,
  simpa only [h.map_zero'] using (has_equalizer_of_equivalence e f 0) hf,
end

lemma has_kernel_iff_of_equivalence [preadditive C] [preadditive D]
  (e : C ≌ D) [functor.additive e.functor] [functor.additive e.inverse]
  {X Y : C} (f : X ⟶ Y) :
  has_kernel f ↔ has_kernel (e.functor.map f) :=
begin
  split,
  { exact has_kernel_of_equivalence e f, },
  { intro hf',
    let F := e.unit_iso.hom.naturality f,
    erw ← comp_id f,
    have hY := congr_app (e.unit_iso.hom_inv_id) Y,
    rw [nat_trans.id_app, nat_trans.comp_app] at hY,
    erw [← hY, ← assoc, F],
    dsimp,
    haveI : functor.additive e.symm.functor := (infer_instance : functor.additive e.inverse),
    haveI : has_kernel (e.inverse.map (e.functor.map f)) :=
      has_kernel_of_equivalence e.symm (e.functor.map f) hf',
    haveI : has_kernel (e.unit_iso.hom.app X ≫ e.inverse.map (e.functor.map f))
      := limits.has_kernel_iso_comp _ _,
    apply limits.has_kernel_comp_mono, },
end

end pseudoabelian

end category_theory