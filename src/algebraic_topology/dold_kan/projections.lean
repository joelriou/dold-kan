/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.faces

/-

# Construction of projections for the Dold-Kan correspondence

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`higher_faces_vanish_P` and `P_is_identity_where_faces_vanish`.

Then, we show that they are projections (see `P_degreewise_is_a_projection`
and `P_is_a_projection`).  They are natural transformations (see `nat_trans_P`
and `P_degreewise_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `p_infty.lean`
in order to define `P_infty : K[X] ⟶ K[X]`, see `equivalence.lean` for the general
strategy of proof of the Dold-Kan equivalence.

-/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.simplicial_object
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

/-- This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`. -/
@[simp]
noncomputable def P : ℕ → (K[X] ⟶ K[X])
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ + Hσ q)

/-- Q q is the complement projection associated to P q -/
def Q (q : ℕ) : K[X] ⟶ K[X] := 𝟙 _ - P q

lemma P_add_Q (q : ℕ) : P q + Q q = 𝟙 K[X] := by { rw Q, abel }

lemma P_add_Q_degreewise (q n : ℕ) : (P q).f n + (Q q).f n = 𝟙 (X _[n]) :=
by simpa only [← homological_complex.add_f_apply, P_add_Q q]

lemma Q_eq_0 : (Q 0 : K[X] ⟶ _) = 0 := sub_self _

lemma Q_eq (q : ℕ) : (Q (q+1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q :=
by { unfold Q P, simp only [comp_add, comp_id], abel, }

/-- All the `Q q` coincide with `0` in degree 0. -/
lemma Q_deg0_eq (q : ℕ) : ((Q q).f 0 : X _[0] ⟶ X _[0]) = 0 :=
begin
  induction q with q hq,
  { simpa only [Q_eq_0], },
  { rw Q_eq,
    simp only [Q_eq, hq, Hσ_eq_zero, homological_complex.sub_f_apply,
      homological_complex.comp_f, comp_zero, sub_zero], }
end

/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
lemma P_deg0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
by conv_rhs { erw [← P_add_Q_degreewise q 0, Q_deg0_eq, add_zero], }

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _[n+1] ⟶ X _[n]` when k≠0 and k≥n-q+2 -/
lemma higher_faces_vanish_P : Π (q : ℕ),
  Π (n : ℕ), higher_faces_vanish q (((P q).f (n+1) : X _[n+1] ⟶ X _[n+1]))
| 0     := λ n j hj₁, by { exfalso, have hj₂ := fin.is_lt j, linarith, }
| (q+1) := λ n, begin
    unfold P,
    exact higher_faces_vanish_induction (higher_faces_vanish_P q n),
  end

lemma P_is_identity_where_faces_vanish {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (P q).f (n+1) = φ :=
begin
  induction q with q hq,
  { unfold P,
    erw comp_id, },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id, ← assoc,
      hq (downgrade_vanishing v), add_right_eq_self],
    by_cases hqn : n<q,
    { exact Hσφ_eq_zero hqn (downgrade_vanishing v), },
    { cases nat.le.dest (not_lt.mp hqn) with a ha,
      have hnaq : n=a+q := by linarith,
      simp only [Hσφ_eq_neg_σδφ hnaq (downgrade_vanishing v), neg_eq_zero, ← assoc],
      have eq := v ⟨a, by linarith⟩ _, swap,
      { have foo := nat.succ_eq_add_one,
        simp only [hnaq, fin.coe_mk, nat.succ_eq_add_one, add_assoc], },
      simp only [fin.succ_mk] at eq,
      simp only [eq, zero_comp], }, },
end

lemma P_degreewise_is_a_projection (q n : ℕ) :
  ((P q).f n : X _[n] ⟶ _) ≫ ((P q).f n) = (P q).f n :=
begin
  cases n,
  { rw [P_deg0_eq q, comp_id], },
  { exact P_is_identity_where_faces_vanish (higher_faces_vanish_P q n), }
end

lemma P_is_a_projection (q : ℕ) : (P q : K[X] ⟶ K[X]) ≫ P q = P q :=
by { ext n, exact P_degreewise_is_a_projection q n, }

/-- For each q, P q is a natural transformation. -/
def nat_trans_P (q : ℕ) :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ X, P q,
  naturality' := λ X Y f, begin
    induction q with q hq,
    { erw [id_comp, comp_id], },
    { unfold P,
      simp only [add_comp, comp_add, assoc, comp_id, hq],
      congr' 1,
      rw [← assoc, hq, assoc],
      congr' 1,
      exact (nat_trans_Hσ q).naturality' f, }
  end }

lemma P_degreewise_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [n]) ≫ (P q).f n = (P q).f n ≫ f.app (op [n]) :=
homological_complex.congr_hom ((nat_trans_P q).naturality f) n

lemma map_P {D : Type*} [category D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (q n : ℕ) :
  ((P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n) = G.map ((P q : K[X] ⟶ _).f n) :=
begin
  induction q with q hq,
  { erw [G.map_id], refl, },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f, homological_complex.add_f_apply,
      comp_id, functor.map_add, functor.map_comp, hq, map_Hσ], }
end

end dold_kan

end algebraic_topology
