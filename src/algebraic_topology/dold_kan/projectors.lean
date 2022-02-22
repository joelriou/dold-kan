/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.faces

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.simplicial_object
open simplex_category
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {C : Type*} [category.{v} C] [preadditive C]
variables {X : simplicial_object C}

/-- This is the inductive definition of the projectors `P q`, with `P 0 := Id` and
`P (q+1) := P q ≫ (𝟙 _ + Hσ q)`.

By our construction, we can take for granted that these are morphisms of chain
complexes, all of which are homotopic to the identity.

We shall give simple formulas for the composition `P q ≫ Hσ q` in lemmas
`Hσφ_eq_neg_σδ` (which involve compositions `δ (a+1) ≫ σ a`) and `Hσφ_eq_zero`.
Instead of inductive definition we have chosen, similarly as the approach in the
mathematical references, we could have your these degreewise formulas in order
to define the sequence of `P q`, but then it would have been necessary to check
that they commute with the differentials. The approach we have chosen saves some
calculations.
-/
@[simp]
noncomputable def P : ℕ → (K[X] ⟶ K[X])
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ + Hσ q)

/-- Q q is the complement projector associated to P q -/
def Q (q : ℕ) : K[X] ⟶ K[X] := 𝟙 _ - P q

lemma P_add_Q (q : ℕ) : P q + Q q = 𝟙 K[X] := by { rw Q, abel }

lemma P_add_Q_degreewise (q n : ℕ) : (P q).f n + (Q q).f n = 𝟙 (X _[n]) :=
by simpa only [← homological_complex.add_f_apply, P_add_Q q]

lemma Q_eq_0 : (Q 0 : K[X] ⟶ _) = 0 := sub_self _

lemma Q_eq (q : ℕ) : (Q (q+1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q :=
by { unfold Q P, simp only [comp_add, comp_id], abel, }

/- All the `P q` coincide with `𝟙` in degree 0. -/
lemma P_deg0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  induction q with q hq,
  { refl, },
  { unfold P,
    simp only [homological_complex.comp_f, homological_complex.add_f_apply,
      homological_complex.id_f, comp_add, id_comp, add_right_eq_self, hq, Hσ_eq_zero], }
end

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _[n+1] ⟶ X _[n]` when k≠0 and k≥n-q+2 -/
lemma higher_faces_vanish_P : Π (q : ℕ),
  Π (n : ℕ), higher_faces_vanish q (((P q).f (n+1) : X _[n+1] ⟶ X _[n+1]))
| 0     := λ n,
  { vanishing := λ j hj₁, by { exfalso, have hj₂ := fin.is_lt j, linarith, } }
| (q+1) := λ n,
  { vanishing := begin
      unfold P,
      exact (higher_faces_vanish_ind (higher_faces_vanish_P q n)).vanishing,
  end }

lemma P_is_identity_where_faces_vanish {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (P q).f (n+1) = φ :=
begin
  induction q with q hq,
  { unfold P,
    erw [homological_complex.id_f, comp_id], },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id, ← assoc,
      hq (downgrade_vanishing v), add_right_eq_self],
    by_cases hqn : n<q,
    { exact Hσφ_eq_zero hqn (downgrade_vanishing v), },
    { cases nat.le.dest (not_lt.mp hqn) with a ha,
      have hnaq : n=a+q := by linarith,
      simp only [Hσφ_eq_neg_σδ hnaq (downgrade_vanishing v), neg_eq_zero, ← assoc],
      have eq := v.vanishing ⟨a, by linarith⟩ _, swap,
      { have foo := nat.succ_eq_add_one,
        simp only [hnaq, fin.coe_mk, nat.succ_eq_add_one, add_assoc], },
      simp only [fin.succ_mk] at eq,
      simp only [eq, zero_comp], }, },
end

lemma P_degreewise_is_a_projector (q n : ℕ) :
  ((P q).f n : X _[n] ⟶ _) ≫ ((P q).f n) = (P q).f n :=
begin
  cases n,
  { rw [P_deg0_eq q, comp_id], },
  { exact P_is_identity_where_faces_vanish (higher_faces_vanish_P q n), }
end

lemma P_is_a_projector (q : ℕ) : (P q : K[X] ⟶ K[X]) ≫ P q = P q :=
by { ext n, exact P_degreewise_is_a_projector q n, }

/-- For each q, P q is a natural transformation. -/
def nat_trans_P (q : ℕ) :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ _, P q,
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

lemma map_P {D : Type*} [category.{v} D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (q n : ℕ) :
  ((P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n) =
    G.map ((P q : K[X] ⟶ _).f n) :=
begin
  induction q with q hq,
  { erw [G.map_id], refl, },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f, homological_complex.add_f_apply, comp_id,
      functor.map_add, functor.map_comp, hq, map_Hσ], }
end

end dold_kan

end algebraic_topology
