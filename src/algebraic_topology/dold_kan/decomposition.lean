/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.p_infty

open category_theory
open category_theory.category
open category_theory.preadditive
open opposite
open_locale big_operators
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

/-- This is the decreasing involution of `fin (n+1)` which appears in `decomposition_Q`. -/
def reverse_fin {n : ℕ} (i : fin (n+1)) : fin (n+1):= ⟨n-i, nat.sub_lt_succ n i⟩

lemma reverse_fin_eq {n a : ℕ} (i : fin(n+1)) (hnaq : n=a+i) : reverse_fin i =
  ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
begin
  ext,
  simp only [reverse_fin, fin.coe_mk],
  exact tsub_eq_of_eq_add hnaq,
end

/-- We decompose the identity using `P_q` and degeneracies. In the case of a simplicial
abelian group, this means we can decompose a $(n+1)$-simplex $x$ as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is in the image of `P_q$ and
the $y_i$ are in degree $n$. -/
lemma decomposition_Q (n q : ℕ) (hqn : q≤n+1) :
  ((Q q).f (n+1) : X _[n+1] ⟶ X _[n+1]) =
  ∑ (i : fin(n+1)) in finset.filter (λ i : fin(n+1), (i:ℕ)<q) finset.univ,
  (P i).f (n+1) ≫ X.δ (reverse_fin i).succ ≫ X.σ (reverse_fin i) :=
begin
  revert hqn,
  induction q with q hq,
  { intro hqn,
    simp only [Q, P, nat.not_lt_zero, finset.sum_empty, finset.filter_false,
      homological_complex.zero_f_apply, sub_self], },
  { intro hqn,
    cases nat.le.dest (nat.succ_le_succ_iff.mp hqn) with a ha,
    rw [Q_eq, homological_complex.sub_f_apply, homological_complex.comp_f,
      hq (nat.le_of_succ_le hqn)],
    symmetry,
    conv { to_rhs, rw [← tactic.ring.add_neg_eq_sub, add_comm], },
    have hqn' := nat.succ_le_iff.mp hqn,
    convert @finset.sum_insert _ _ (finset.filter (λ i : fin(n+1), (i:ℕ)<q) finset.univ)
      ⟨q, hqn'⟩ _ _ _ _,
    { ext i,
      simp only [finset.mem_insert, finset.mem_filter, finset.mem_univ, true_and],
      split,
      { intro hi,
        by_cases (i : ℕ)<q,
        { exact or.inr h, },
        { apply or.inl,
          ext,
          exact nat.eq_of_le_of_lt_succ (not_lt.mp h) hi, }, },
      { intro hi,
        cases hi,
        { rw hi,
          exact lt_add_one q, },
        { exact nat.lt.step hi, }, }, },
    { simp only [fin.coe_mk],
      have hnaq' : n = a+q := by linarith,
      simpa only [Hσφ_eq_neg_σδφ hnaq' (higher_faces_vanish_P q n), reverse_fin_eq ⟨q, hqn'⟩ hnaq', neg_neg], },
    { simp only [finset.mem_filter, fin.coe_mk, lt_self_iff_false,
        and_false, not_false_iff], }, },
end

variable (X)

/-- The structure `morph_components` is an ad hoc structure that is used the
proof of `normalized_Moore_complex_reflects_iso`. The fields are the data
that are needed in order to construct a morphism `X _[n+1] ⟶ Z` (see `F`)
using the decomposition of the identity given by `decomposition_Q n (n+1)`.

In the proof of `normalized_Moore_complex_reflects_iso`, in order to check
that two maps coincide, we only need to verify that the `morph_components`
they come from are equal.
-/
@[ext, nolint has_inhabited_instance]
structure morph_components (n : ℕ) (Z : C) :=
  (a : X _[n+1] ⟶ Z) (b : fin(n+1) → (X _[n] ⟶ Z))

variable {X}
/-- The morphism `X _[n+1] ⟶ Z ` associated to a `morph_components X n Z`-/
def F {Z : C} {n : ℕ} (f : morph_components X n Z) :
  X _[n+1] ⟶ Z := P_infty.f (n+1) ≫ f.a +
  ∑ (i : fin (n+1)), (((P i).f (n+1)) ≫ (X.δ (reverse_fin i).succ) ≫ (f.b (reverse_fin i)))

variable (X)
/-- the canonical `morph_components` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
@[simps]
def morph_components_id (n : ℕ) : morph_components X n (X _[n+1]) :=
{ a := P_infty.f (n+1),
  b := λ i, X.σ i, }

lemma F_id (n : ℕ) : F (morph_components_id X n) = 𝟙 _ :=
begin
  simp only [← P_add_Q_degreewise (n+1) (n+1), F],
  congr' 1,
  { simp only [morph_components_id, P_infty_degreewise, P_degreewise_is_a_projection], },
  { convert (decomposition_Q n (n+1) rfl.le).symm,
    ext i,
    simpa only [finset.mem_univ, finset.mem_filter, true_and, true_iff] using fin.is_lt i, },
end

variable {X}

/-- A `morph_components` can be postcomposed with a map `Z ⟶ Z'`. -/
@[simps]
def morph_components_comp {n : ℕ} {Z Z' : C}
  (f : morph_components X n Z) (g : Z ⟶ Z') : morph_components X n Z' :=
{ a := f.a ≫ g,
  b := λ i, f.b i ≫ g }

lemma F_comp {n : ℕ} {Z Z' : C} (f : morph_components X n Z)
  (g : Z ⟶ Z') : F (morph_components_comp f g) = F f ≫ g :=
begin
  unfold F morph_components_comp,
  simp only [add_comp, sum_comp, assoc],
end

/-- A `morph_components` can be precomposed with a map `X' ⟶ X`. -/
@[simps]
def comp_morph_components {X' X : simplicial_object C} {n : ℕ} {Z : C}
  (g : X' ⟶ X) (f : morph_components X n Z) : morph_components X' n Z :=
{ a := g.app (op [n+1]) ≫ f.a,
  b := λ i, g.app (op [n]) ≫ f.b i }

lemma comp_F {X' X : simplicial_object C} {n : ℕ} {Z : C}
  (g : X' ⟶ X) (f : morph_components X n Z) :
  F (comp_morph_components g f) = g.app (op [n+1]) ≫ F f :=
begin
  unfold F comp_morph_components,
  simp only [P_infty_degreewise, comp_add],
  congr' 1,
  { simp only [← assoc, P_degreewise_naturality], },
  { simp only [comp_sum],
    congr,
    ext,
    slice_rhs 1 2 { rw P_degreewise_naturality, },
    slice_lhs 2 3 { erw g.naturality, },
    simp only [assoc],
    refl, }
end

end dold_kan

end algebraic_topology
