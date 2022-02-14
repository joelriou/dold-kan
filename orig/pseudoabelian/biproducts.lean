/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import pseudoabelian.basic
import category_theory.limits.shapes.biproducts

noncomputable theory

open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.pseudoabelian.karoubi

namespace category_theory

namespace pseudoabelian

namespace karoubi

variables {C : Type*} [category C] [preadditive C]
variables {J : Type*} [decidable_eq J] [fintype J] (F : J → karoubi C)
variables [has_finite_biproducts C]

namespace biproducts

abbreviation biconeX := biproduct.bicone (λ j, (F j).X)

abbreviation biconeX_p := biproduct.map (λ j, (F j).p)

lemma biconeX_p_idempotence : biconeX_p F ≫ biconeX_p F = biconeX_p F :=
begin
  ext j,
  simp only [limits.biproduct.ι_map_assoc, limits.biproduct.ι_map],
  slice_lhs 1 2 { rw (F j).idempotence, },
end

@[simps]
def bicone : limits.bicone F :=
{ X :=
  { X := (biconeX F).X,
    p := (biconeX_p F),
      idempotence := biconeX_p_idempotence F, },
  π := λ j, ⟨biconeX_p F ≫ (biconeX F).π j,
    by { simp only [limits.biproduct.map_π_assoc, category.assoc,
      limits.biproduct.map_π, (F j).idempotence], }⟩,
  ι := λ j, ⟨(biconeX F).ι j ≫ biconeX_p F,
    by { simp only [limits.biproduct.ι_map, category.assoc],
      slice_rhs 1 3 { rw [(F j).idempotence, (F j).idempotence], }, }⟩,
  ι_π := λ j j', begin
    split_ifs,
    { subst h,
      simp only [limits.biproduct.bicone_ι, limits.biproduct.ι_map,
        limits.biproduct.bicone_π, limits.biproduct.ι_π_self_assoc,
        comp, category.assoc, eq_to_hom_refl,
      limits.biproduct.map_π, id_eq, (F j).idempotence], },
    { simp only [comp],
      conv { to_lhs, congr, rw assoc, congr, skip, rw ← assoc, congr,
        rw biconeX_p_idempotence, },
      simp only [limits.biproduct.bicone_ι, limits.biproduct.bicone_π,
        limits.biproduct.map_π],
      conv { to_lhs, congr, rw ← assoc, congr, rw (biconeX F).ι_π, },
      split_ifs,
      simp only [hom_eq_zero_iff, zero_comp], },
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
        simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f, assoc, comp, biproduct.map_π],
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

end karoubi

end pseudoabelian

end category_theory
