/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.normalized

/-
# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`inclusion_of_Moore_complex_is_homotopy_equiv` between the normalized Moore complex
and the alternating face map complex of a simplicial object in `A`.

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.idempotents
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {C : Type*} [category.{v} C] [preadditive C]
variables (X : simplicial_object C)

/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
noncomputable def P_is_homotopic_to_id : Π (q : ℕ),
  homotopy (P q : K[X] ⟶ _) (𝟙 _)
| 0     := homotopy.refl _
| (q+1) :=
  begin
    have h := homotopy.add (P_is_homotopic_to_id q)
      (homotopy.comp_left (homotopy_Hσ_to_zero q) (P q)),
    refine homotopy.trans (homotopy.of_eq _) (homotopy.trans h (homotopy.of_eq _)),
    { unfold P, simp only [comp_add, comp_id], },
    { simp only [add_zero, comp_zero], },
  end

/-- The complement projection `Q q` to `P q` are homotopic to zero. -/
def Q_is_homotopic_to_zero (q : ℕ) : homotopy (Q q : K[X] ⟶ _) 0 :=
homotopy.equiv_sub_zero.to_fun (P_is_homotopic_to_id X q).symm

lemma homotopies_P_id_are_eventually_constant {q : ℕ} {n : ℕ} (hqn : n<q):
  ((P_is_homotopic_to_id X (q+1)).hom n (n+1) : X _[n] ⟶ X _[n+1]) =
  (P_is_homotopic_to_id X q).hom n (n+1) :=
begin
  unfold P_is_homotopic_to_id,
  simp only [homotopy.trans_hom, pi.add_apply, homotopy.of_eq_hom, pi.zero_apply,
    graded_object.zero_apply, homotopy.add_hom, homotopy.comp_left_hom, add_zero,
    zero_add, add_right_eq_self, homotopy_Hσ_to_zero, homotopy.null_homotopy'_hom,
    complex_shape.down_rel, eq_self_iff_true, dif_pos],
  erw [hσ'_eq_zero hqn (c_mk (n+1) n rfl), comp_zero],
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
        zero_add, homological_complex.id_f, P_infty_f, P_f_0_eq] at h ⊢,
      erw ← h, },
    { have h := (P_is_homotopic_to_id X (n+2)).comm (n+1),
      simp only [homotopy.d_next_succ_chain_complex, homotopy.prev_d_chain_complex,
        homological_complex.id_f, P_infty_f] at h ⊢,
      erw [homotopies_P_id_are_eventually_constant X (lt_add_one (n+1)), ← h],
      rw ← P_is_eventually_constant (rfl.le : n+1 ≤ n+1), },
  end }

/-- The inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[simps]
def inclusion_of_Moore_complex_is_homotopy_equiv {A : Type*} [category A] [abelian A]
  {Y : simplicial_object A} : homotopy_equiv ((normalized_Moore_complex A).obj Y)
  ((alternating_face_map_complex A).obj Y) :=
{ hom := inclusion_of_Moore_complex_map Y,
  inv := P_infty_into_Moore_subcomplex Y,
  homotopy_hom_inv_id := homotopy.of_eq (split_mono_inclusion_of_Moore_complex Y).id,
  homotopy_inv_hom_id := homotopy.trans (homotopy.of_eq
    (P_infty_into_Moore_subcomplex_comp_inclusion Y)) (P_infty_is_homotopic_to_id Y), }

end dold_kan

end algebraic_topology
