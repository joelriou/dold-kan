/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.images
import for_mathlib.simplex_category.factorisations
import category_theory.limits.shapes.finite_products
import algebraic_topology.simplicial_set
import category_theory.limits.preserves.shapes.products
import algebraic_topology.split_simplicial_object
import for_mathlib.inclusions_mono

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite
open simplex_category
open_locale simplicial

universe u

variables {C : Type*} [category C]

namespace simplicial_object

namespace splitting

namespace index_set

variables {Δ : simplex_categoryᵒᵖ} (A : index_set Δ)

lemma eq_id_iff_len_le : A.eq_id ↔ Δ.unop.len ≤ A.1.unop.len :=
begin
  split,
  { intro h,
    rw eq_id_iff_len_eq at h,
    rw h, },
  { intro h,
    rw eq_id_iff_len_eq,
    refine le_antisymm (len_le_of_epi (infer_instance : epi A.e)) h, },
end

lemma eq_id_iff_mono : A.eq_id ↔ mono A.e :=
begin
  split,
  { intro h,
    dsimp at h,
    subst h,
    dsimp only [id, e],
    apply_instance, },
  { intro h,
    rw eq_id_iff_len_le,
    exact len_le_of_mono h, }
end

end index_set

end splitting

end simplicial_object
