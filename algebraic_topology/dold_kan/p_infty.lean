/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.projectors

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open simplex_category
open_locale simplicial

noncomputable theory


namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

lemma P_is_eventually_constant {q n : ℕ} (hqn : n≤q) :
  ((P (q+1)).f n : X _[n] ⟶ _ ) = (P q).f n :=
begin
  cases n,
  { simp only [P_deg0_eq], },
  { unfold P,
    simp only [add_right_eq_self, comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id],
    exact Hσφ_eq_zero (nat.succ_le_iff.mp hqn) (higher_faces_vanish_P q n), }
end

/-- Definition of P_infty from the P q -/
def P_infty : K[X] ⟶ K[X] := chain_complex.of_hom _ _ _ _ _ _
    (λ n, ((P n).f n : X _[n] ⟶ _ ))
begin
  intro n,
  simp only [← P_is_eventually_constant (rfl.ge : n≤n)],
  have eq := (P (n+1) : K[X] ⟶ _).comm (n+1) n,
  erw chain_complex.of_d at eq,
  exact eq,
end

lemma P_infty_termwise (n : ℕ) : (P_infty.f n : X _[n] ⟶  X _[n] ) =
  (P n).f n := by refl

lemma P_infty_termwise_is_a_projector (n : ℕ) :
  (P_infty.f n : X _[n] ⟶ _) ≫ (P_infty.f n) = P_infty.f n :=
by simp only [P_infty_termwise, ← homological_complex.comp_f, P_is_a_projector n]

lemma P_infty_is_a_projector : (P_infty : K[X] ⟶ _) ≫ P_infty = P_infty :=
by { ext n, exact P_infty_termwise_is_a_projector n, }

end dold_kan

end algebraic_topology
