/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.normalized

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.idempotents
--open category_theory.simplicial_object
--open homotopy
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {C : Type*} [category.{v} C] [preadditive C]
variables (X : simplicial_object C)

/-- inductive construction of homotopies from `P q` to `𝟙` -/
noncomputable def P_is_homotopic_to_id : Π (q : ℕ),
  homotopy (P q : K[X] ⟶ _) (𝟙 _)
| 0     := homotopy.refl _
| (q+1) :=
  begin
    have h := homotopy.add (P_is_homotopic_to_id q)
      (homotopy.comp_left (homotopy_Hσ_to_zero X q) (P q)),
    refine homotopy.trans (homotopy.of_eq _) (homotopy.trans h (homotopy.of_eq _)),
    { unfold P, simp only [comp_add, comp_id], },
    { simp only [add_zero, comp_zero], },
  end

def Q_is_homotopic_to_zero (q : ℕ) : homotopy (Q q : K[X] ⟶ _) 0 :=
homotopy.equiv_sub_zero.to_fun (P_is_homotopic_to_id X q).symm

lemma homotopies_P_id_are_eventually_constant {q : ℕ} {n : ℕ} (hqn : n<q):
  ((P_is_homotopic_to_id X (q+1)).hom n (n+1) : X _[n] ⟶ X _[n+1]) =
  (P_is_homotopic_to_id X q).hom n (n+1) :=
begin
  unfold P_is_homotopic_to_id,
  simp only [homotopy_Hσ_to_zero, complex_shape.down_rel, eq_self_iff_true,
    homotopy.trans_hom, pi.add_apply, homotopy.of_eq_hom, pi.zero_apply,
    homotopy.add_hom, homotopy.comp_left_hom, homotopy.null_homotopy'_hom,
    dif_pos, add_zero, zero_add, add_right_eq_self],
  erw [hσ'_eq_zero hqn (cs_down_succ n), comp_zero],
end

variable (X)

/-- Construction of the homotopy from `P_infty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all q -/
@[simps]
def P_infty_is_homotopic_to_id :
  homotopy (P_infty : K[X] ⟶ _) (𝟙 _) :=
{ hom := λ i j, (P_is_homotopic_to_id X (j+1)).hom i j,
  zero' := λ i j hij, homotopy.zero _ i j hij,
  comm := λ n, begin
    cases n,
    { have h := (P_is_homotopic_to_id X 2).comm 0,
      simp only [homotopy.d_next_zero_chain_complex, homotopy.prev_d_chain_complex,
        zero_add, homological_complex.id_f, P_infty_degreewise, P_deg0_eq] at h ⊢,
      erw ← h, },
    { have h := (P_is_homotopic_to_id X (n+2)).comm (n+1),
      simp only [homotopy.d_next_succ_chain_complex, homotopy.prev_d_chain_complex,
        homological_complex.id_f, P_infty_degreewise] at h ⊢,
      erw [homotopies_P_id_are_eventually_constant X (lt_add_one (n+1)), ← h],
      rw ← P_is_eventually_constant (rfl.ge : n+1 ≤ n+1), },
  end }

/-- the inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[simps]
def homotopy_equiv_inclusion_of_Moore_complex {A : Type*} [category A] [abelian A]
  {Y : simplicial_object A}:
  homotopy_equiv ((normalized_Moore_complex A).obj Y)
    ((alternating_face_map_complex A).obj Y) :=
{ hom := inclusion_of_Moore_complex_map Y,
  inv := P_infty_into_Moore_subcomplex Y,
  homotopy_hom_inv_id := homotopy.of_eq (P_infty_is_a_retraction Y),
  homotopy_inv_hom_id := homotopy.trans (homotopy.of_eq (factors_P_infty Y))
      (P_infty_is_homotopic_to_id Y), }

/- Unnecessary
@[simps]
def inclusion_N₂ : (N₂ : karoubi (simplicial_object C) ⥤ _ ) ⟶
  (functor_extension'' _ _).obj (alternating_face_map_complex C) :=
{ app := λ X,
  { f := (alternating_face_map_complex C).map X.p ≫ P_infty,
    comm := begin
      ext n,
      simp only [alternating_face_map_complex.map, alternating_face_map_complex_map,
        homological_complex.comp_f, chain_complex.of_hom_f,
        functor_extension''_obj_obj_p, assoc, N₂_obj_p_f],
      have h := P_infty_degreewise_naturality n X.p,
      have h' := congr_app X.idempotence (op [n]),
      simp only [nat_trans.comp_app] at h',
      slice_rhs 1 2 { erw ← h, },
      slice_rhs 2 3 { erw ← h, },
      slice_rhs 3 4 { erw P_infty_degreewise_is_a_projector n, },
      slice_rhs 3 4 { erw ← h, },
      slice_rhs 1 3 { erw [h', h'], },
    end },
  naturality' := λ X Y f, begin
    ext n,
    simp only [alternating_face_map_complex.map, alternating_face_map_complex_map,
      homological_complex.comp_f, chain_complex.of_hom_f, assoc, karoubi.comp,
      N₂_map_f_f, functor_extension''_obj_map_f],
    slice_lhs 3 4 { rw P_infty_degreewise_naturality n Y.p, },
    slice_lhs 2 3 { rw P_infty_degreewise_naturality n f.f, },
    slice_lhs 1 2 { erw P_infty_degreewise_is_a_projector n, },
    slice_rhs 1 2 { rw P_infty_degreewise_naturality n X.p, },
    simp only [assoc, ← nat_trans.comp_app, karoubi.p_comm f],
  end }

@[simps]
def retraction_N₂ : (functor_extension'' _ _).obj (alternating_face_map_complex C)
  ⟶ (N₂ : karoubi (simplicial_object C) ⥤ _ ) :=
{ app := λ X,
  { f := (alternating_face_map_complex C).map X.p ≫ P_infty,
    comm := begin
      ext n,
      simp only [alternating_face_map_complex.map, alternating_face_map_complex_map,
        homological_complex.comp_f, chain_complex.of_hom_f, functor_extension''_obj_obj_p,
        assoc, N₂_obj_p_f],
      have h := P_infty_degreewise_naturality n X.p,
      have h' := congr_app X.idempotence (op [n]),
      simp only [nat_trans.comp_app] at h',
      slice_rhs 3 4 { erw P_infty_degreewise_is_a_projector n, },
      slice_rhs 3 4 { erw ← h, },
      slice_rhs 1 3 { erw [h', h'], },
    end },
  naturality' := λ X Y f, begin
    ext n,
    simp only [alternating_face_map_complex.map, alternating_face_map_complex_map,
      homological_complex.comp_f, chain_complex.of_hom_f, assoc,
      functor_extension''_obj_map_f, karoubi.comp, N₂_map_f_f],
    slice_rhs 2 3 { erw P_infty_degreewise_is_a_projector n, },
    slice_rhs 2 3 { erw ← P_infty_degreewise_naturality n f.f, },
    simp only [← assoc, ← nat_trans.comp_app, karoubi.p_comm f],
  end }

def inclusion_N_comp_retraction_N : inclusion_N₂ ≫ retraction_N₂ =
  𝟙 (N₂ : karoubi (simplicial_object C) ⥤ _) :=
begin
  ext P n,
  simp only [inclusion_N₂_app_f, alternating_face_map_complex.map,
    alternating_face_map_complex_map, retraction_N₂_app_f, assoc,
    nat_trans.comp_app, karoubi.comp, homological_complex.comp_f,
    chain_complex.of_hom_f, nat_trans.id_app, karoubi.id_eq, N₂_obj_p_f],
  have h := P_infty_degreewise_naturality n P.p,
  have h' := congr_app P.idempotence (op [n]),
  simp only [nat_trans.comp_app] at h',
  slice_lhs 1 2 { erw h, },
  slice_lhs 2 3 { erw h', },
  slice_lhs 2 3 { erw h, },
  slice_lhs 1 2 { erw P_infty_degreewise_is_a_projector n, },
end

private def τ' := (karoubi_chain_complex_equivalence C ℕ).functor
private def τ : karoubi (simplicial_object C) ⥤ simplicial_object (karoubi C) :=
  (karoubi_functor_category_embedding simplex_categoryᵒᵖ C)

lemma karoubi_compatibility_K :
  (functor_extension'' _ _).obj (alternating_face_map_complex C) ⋙ τ' =
  τ ⋙ alternating_face_map_complex (karoubi C) :=
begin
  apply category_theory.functor.ext,
  { intros X Y f,
    ext n,
    simpa only [functor.comp_map, karoubi.comp_p, karoubi.p_comp, alternating_face_map_complex.map,
      alternating_face_map_complex_map, homological_complex.comp_f, homological_complex.eq_to_hom_f,
      eq_to_hom_refl, karoubi.id_eq, chain_complex.of_hom_f, karoubi.comp], },
  { intro P,
    ext i j hij,
    { have eq : j+1 = i := hij,
      subst eq,
      erw [comp_id, id_comp, karoubi_alternating_face_map_complex_d P j],
      dsimp [τ', karoubi_chain_complex_equivalence],
      erw [← ((alternating_face_map_complex C).map P.p).comm' (j+1) j hij, ← assoc],
      congr',
      exact congr_app P.idempotence.symm (op [j+1]), },
    { refl, }, },
end

lemma karoubi_compatibility_P_infty (P : karoubi (simplicial_object C)) :
  τ'.map (retraction_N₂.app P) ≫ τ'.map (inclusion_N₂.app P) =
  eq_to_hom (by {exact congr_obj karoubi_compatibility_K P, }) ≫ P_infty ≫
    eq_to_hom (congr_obj karoubi_compatibility_K P).symm :=
begin
  ext n,
  rw ← τ'.map_comp,
  dsimp [τ'],
  simp only [retraction_N₂_app_f, alternating_face_map_complex.map,
    alternating_face_map_complex_map, inclusion_N₂_app_f, assoc, karoubi.comp,
    homological_complex.comp_f, chain_complex.of_hom_f, karoubi.comp_p,
    karoubi_chain_complex_equivalence_functor_obj_X_p, functor_extension''_obj_obj_p,
    homological_complex.eq_to_hom_f, eq_to_hom_refl, karoubi.id_eq],
  erw karoubi_P_infty_f,
  slice_lhs 2 3 { erw ← P_infty_degreewise_naturality n P.p, },
  slice_lhs 3 4 { erw P_infty_degreewise_is_a_projector, },
end

def homotopy_equiv_inclusion_N (P : karoubi (simplicial_object C)) :
homotopy_equiv (τ'.obj (N₂.obj P))
(τ'.obj (((functor_extension'' _ _).obj (alternating_face_map_complex C)).obj P)) :=
{ hom := τ'.map (inclusion_N₂.app P),
  inv := τ'.map (retraction_N₂.app P),
  homotopy_hom_inv_id := begin
    convert homotopy.refl (𝟙 _),
    rw ← τ'.map_comp,
    convert τ'.map_id _,
    rw ← nat_trans.comp_app,
    rw inclusion_N_comp_retraction_N,
    refl,
  end,
  homotopy_inv_hom_id := begin
    erw karoubi_compatibility_P_infty P,
    have eq : _ = K[_] := congr_obj karoubi_compatibility_K P,
    convert homotopy.comp (homotopy.refl (eq_to_hom eq))
      (homotopy.comp (P_infty_is_homotopic_to_id _) (homotopy.refl (eq_to_hom eq.symm))),
    simpa only [id_comp, eq_to_hom_trans, eq_to_hom_refl],
  end }-/

end dold_kan

end algebraic_topology
