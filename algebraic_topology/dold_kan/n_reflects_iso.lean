/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functor_n
import algebraic_topology.dold_kan.decomposition
import category_theory.idempotents.karoubi_karoubi

open category_theory
open category_theory.category
open category_theory.idempotents
open opposite
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

instance : reflects_isomorphisms
  (N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
begin
  refine ⟨_⟩,
  intros X Y f,
  introI,
  /- restating the result in a way that allows induction on the degree n -/
  haveI : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (f.app Δ), swap,
  { exact nat_iso.is_iso_of_is_iso_app f, },
  intro Δ,
  let m := simplex_category.len (unop Δ),
  rw [show Δ = op [m], by { simp only [op_unop, simplex_category.mk_len], }],
  generalize : m = n, clear m Δ,
  /- rewriting some assumptions in a more practical form -/
  have h  := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.hom_inv_id (N'.map f))),
  have h' := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.inv_hom_id (N'.map f))),
  simp only [N'_map, homological_complex.comp_f, chain_complex.of_hom_f, assoc,
    karoubi.id_eq, karoubi.comp, alternating_face_map_complex_map,
    alternating_face_map_complex.map] at h h',
  dsimp at h h',
  /- we have to construct an inverse to f in degree n, by induction on n -/
  induction n with n hn,
  /- degree 0 -/
  { use (inv (N'.map f)).f.f 0,
    split,
    have eq := h 0, swap,
    have eq := h' 0,
    all_goals
    { simp only [P_infty_degreewise, P_deg0_eq] at eq,
      erw id_comp at eq,
      exact eq, }, },
  /- isomorphism in degree n+1 of an isomorphism in degree n -/
  { haveI := hn,
    use F
      { a := P_infty.f (n+1) ≫ (inv (N'.map f)).f.f (n+1),
        b := λ i, inv (f.app (op [n])) ≫ X.σ i, },
    split,
    { rw [← F_id, ← comp_F],
      simp only [comp_morph_components, morph_components_id],
      congr' 2,
      { erw [← assoc, P_infty_degreewise_naturality],
        exact h (n+1), },
      { ext,
        rw ← assoc,
        simp only [id_comp, is_iso.hom_inv_id], }, },
    { rw [← F_id, ← F_comp],
      simp only [morph_components_comp, morph_components_id],
      congr' 2,
      { have eq := homological_complex.congr_hom (karoubi.p_comp (inv (N'.map f))) (n+1),
        have eq' := homological_complex.congr_hom (karoubi.comp_p (inv (N'.map f))) (n+1),
        simp only [homological_complex.comp_f] at eq eq',
        erw [eq, ← eq', assoc],
        exact h' (n+1), },
      { ext,
        erw [assoc, f.naturality, ← assoc, is_iso.inv_hom_id, id_comp],
        refl, }, }, }
end

instance : reflects_isomorphisms
  (N : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)) :=
begin
  refine ⟨_⟩,
  intros X Y f,
  introI,
  let F1 := karoubi_functor_category_embedding simplex_categoryᵒᵖ C,
  let F2 : simplicial_object (karoubi C) ⥤ _ := N',
--  let F3 := (karoubi_chain_complex_equivalence (karoubi C) ℕ).functor,
  let F4 := functor.map_homological_complex (karoubi_karoubi.equivalence C).inverse
    (complex_shape.down ℕ),

  sorry,
end

end dold_kan

end algebraic_topology
