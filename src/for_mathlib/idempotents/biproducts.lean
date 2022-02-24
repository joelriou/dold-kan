/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.idempotents.karoubi
import category_theory.additive.basic

noncomputable theory

open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.idempotents

universe v

namespace category_theory

namespace idempotents

namespace karoubi

variables {C : Type*} [category.{v} C] [preadditive C]
variables {J : Type v} [decidable_eq J] [fintype J] (F : J → karoubi C)
variables [has_finite_biproducts C]

namespace biproducts

@[simps]
def bicone : limits.bicone F :=
{ X :=
  { X := (biproduct.bicone (λ j, (F j).X)).X,
    p := biproduct.map (λ j, (F j).p),
    idempotence := begin
      ext j,
      simp only [limits.biproduct.ι_map_assoc, limits.biproduct.ι_map],
      slice_lhs 1 2 { rw (F j).idempotence, },
    end, },
  π := λ j,
    { f := biproduct.map (λ j, (F j).p) ≫ bicone.π _ j,
      comm := by simp only [assoc, biproduct.bicone_π, biproduct.map_π,
        biproduct.map_π_assoc, (F j).idempotence], },
  ι := λ j,
    { f := (by exact bicone.ι _ j) ≫ biproduct.map (λ j, (F j).p),
      comm := by rw [biproduct.ι_map, ← assoc, ← assoc, (F j).idempotence,
        assoc, biproduct.ι_map, ← assoc, (F j).idempotence], },
  ι_π := λ j j', begin
    split_ifs,
    { subst h,
      simp only [limits.biproduct.bicone_ι, limits.biproduct.ι_map,
        limits.biproduct.bicone_π, limits.biproduct.ι_π_self_assoc,
        comp, category.assoc, eq_to_hom_refl, id_eq,
        limits.biproduct.map_π, (F j).idempotence], },
    { simpa only [hom_ext, limits.biproduct.ι_π_ne_assoc _ h, assoc,
        biproduct.map_π, biproduct.map_π_assoc, zero_comp, comp], },
  end, }

end biproducts

instance : has_finite_biproducts (karoubi C) :=
{ has_biproducts_of_shape := λ J hJ1 hJ2,
  { has_biproduct := λ F, begin
    letI := hJ2,
    apply has_biproduct_of_total (biproducts.bicone F),
    ext1, ext1,
    simp only [id_eq, comp_id, biproducts.bicone_X_p,
      limits.biproduct.ι_map],
    rw [sum_hom, comp_sum],
    rw finset.sum_eq_single j, rotate,
    { intros j' h1 h2,
      simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f,
        assoc, comp, biproduct.map_π],
      slice_lhs 1 2 { rw biproduct.ι_π, },
      split_ifs,
      { exfalso, exact h2 h.symm, },
      { simp only [zero_comp], } },
    { intro h1,
      exfalso,
      simpa only [finset.mem_univ, not_true] using h1, },
    simp only [biproducts.bicone_π_f, comp,
      biproduct.ι_map, assoc, biproducts.bicone_ι_f, biproduct.map_π],
    slice_lhs 1 2 { rw biproduct.ι_π, },
    split_ifs, swap, { exfalso, exact h rfl, },
    simp only [eq_to_hom_refl, id_comp, (F j).idempotence],
  end, } }

instance {D : Type*} [category D] [additive_category D] : additive_category (karoubi D) := { }

#check 42

variable (P : karoubi C)

@[simps]
def supplement : karoubi C :=
{ X := P.X,
  p := 𝟙 _ - P.p,
  idempotence := idempotence_of_id_sub_idempotent P.p P.idempotence, }

instance : has_binary_biproduct P P.supplement := has_binary_biproduct_of_total
{ X := P.X,
  fst := P.decomp_id_p,
  snd := P.supplement.decomp_id_p,
  inl := P.decomp_id_i,
  inr := P.supplement.decomp_id_i,
  inl_fst' := P.decomp_id.symm,
  inl_snd' := begin
    simp only [decomp_id_i_f, decomp_id_p_f, supplement_p, comp_sub, comp,
      hom_ext, quiver.hom.add_comm_group_zero_f, P.idempotence],
      erw [comp_id, sub_self],
  end,
  inr_fst' := begin
    simp only [decomp_id_i_f, supplement_p, decomp_id_p_f, sub_comp, comp,
      hom_ext, quiver.hom.add_comm_group_zero_f, P.idempotence],
      erw [id_comp, sub_self],
  end,
  inr_snd' := P.supplement.decomp_id.symm, }
(by simp only [hom_ext, ← decomp_p, quiver.hom.add_comm_group_add_f,
  to_karoubi_map_f, id_eq, coe_p, supplement_p, add_sub_cancel'_right])

def decomposition : P ⊞ P.supplement ≅ (to_karoubi _).obj P.X :=
{ hom := biprod.desc P.decomp_id_i P.supplement.decomp_id_i,
  inv := biprod.lift P.decomp_id_p P.supplement.decomp_id_p,
  hom_inv_id' := begin
    ext1,
    { simp only [← assoc, biprod.inl_desc, comp_id, biprod.lift_eq, comp_add,
        ← decomp_id, id_comp, add_right_eq_self],
      convert zero_comp,
      ext,
      simp only [decomp_id_i_f, decomp_id_p_f, supplement_p, comp_sub, comp,
        quiver.hom.add_comm_group_zero_f, P.idempotence],
      erw [comp_id, sub_self], },
    { simp only [← assoc, biprod.inr_desc, biprod.lift_eq, comp_add,
        ← decomp_id, comp_id, id_comp, add_left_eq_self],
      convert zero_comp,
      ext,
      simp only [decomp_id_i_f, decomp_id_p_f, supplement_p, sub_comp, comp,
        quiver.hom.add_comm_group_zero_f, P.idempotence],
      erw [id_comp, sub_self], }
  end,
  inv_hom_id' := begin
    rw biprod.lift_desc,
    simp only [← decomp_p],
    ext,
    dsimp only [supplement, to_karoubi],
    simp only [quiver.hom.add_comm_group_add_f, add_sub_cancel'_right, id_eq],
  end, }

end karoubi

end idempotents

end category_theory
