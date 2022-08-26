/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import for_mathlib.dold_kan.p_infty
import for_mathlib.simplicial_object

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
variables {X X' : simplicial_object C}

/-- This is the decreasing involution of `fin (n+1)` which appears in `decomposition_Q`. -/
def reverse_fin {n : ℕ} (i : fin (n+1)) : fin (n+1):= ⟨n-i, nat.sub_lt_succ n i⟩

lemma reverse_fin_eq {n a : ℕ} (i : fin (n+1)) (hnaq : n=a+i) : reverse_fin i =
  ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
by { ext, exact tsub_eq_of_eq_add hnaq, }

/-- In each positive degree, this lemma decomposes the idempotent endomorphism
`Q q` as a sum of morphisms which are postcompositions with suitable degeneracies.
As `Q q` is the complement projection to `P q`, this implies that in the case of
simplicial abelian groups, any $(n+1)$-simplex $x$ can be decomposed as
$x = x' + \sum (i=0}^{q-1} σ_{n-i}(y_i)$ where $x'$ is the image of `P q` and
the $y_i$ are in degree $n$. -/
lemma decomposition_Q (n q : ℕ) :
  ((Q q).f (n+1) : X _[n+1] ⟶ X _[n+1]) =
  ∑ (i : fin (n+1)) in finset.filter (λ i : fin(n+1), (i:ℕ)<q) finset.univ,
    (P i).f (n+1) ≫ X.δ (reverse_fin i).succ ≫ X.σ (reverse_fin i) :=
begin
  induction q with q hq,
  { simp only [Q_eq_zero, homological_complex.zero_f_apply, nat.not_lt_zero,
      finset.filter_false, finset.sum_empty], },
  { by_cases hqn : q+1 ≤ n+1, swap,
    { rw [Q_is_eventually_constant (show n+1≤q, by linarith), hq],
      congr,
      ext,
      have hx := x.is_lt,
      simp only [nat.succ_eq_add_one],
      split; intro h; linarith, },
    { cases nat.le.dest (nat.succ_le_succ_iff.mp hqn) with a ha,
      rw [Q_eq, homological_complex.sub_f_apply, homological_complex.comp_f, hq],
      symmetry,
      conv_rhs { rw [sub_eq_add_neg, add_comm], },
      let q' : fin (n+1) := ⟨q, nat.succ_le_iff.mp hqn⟩,
      convert finset.sum_insert ( _ : q' ∉ _),
      { ext i,
        simp only [finset.mem_insert, finset.mem_filter, finset.mem_univ, true_and,
          nat.lt_succ_iff_lt_or_eq, fin.ext_iff],
        tauto, },
      { have hnaq' : n = a+q := by linarith,
        simpa only [fin.coe_mk, (higher_faces_vanish.of_P q n).comp_Hσ_eq hnaq',
          reverse_fin_eq q' hnaq', neg_neg], },
      { simp only [finset.mem_filter, fin.coe_mk, lt_self_iff_false,
            and_false, not_false_iff], }, }, },
end

variable (X)

/-- The structure `morph_components` is an ad hoc structure that is used in
the proof that `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ))`
reflects isomorphisms. The fields are the data that are needed in order to
construct a morphism `X _[n+1] ⟶ Z` (see `φ`) using the decomposition of the
identity given by `decomposition_Q n (n+1)`. -/
@[ext, nolint has_nonempty_instance]
structure morph_components (n : ℕ) (Z : C) :=
(a : X _[n+1] ⟶ Z) (b : fin (n+1) → (X _[n] ⟶ Z))

namespace morph_components

variables {X} {n : ℕ} {Z Z' : C} (f : morph_components X n Z) (g : X' ⟶ X) (h : Z ⟶ Z')
/-- The morphism `X _[n+1] ⟶ Z ` associated to `f : morph_components X n Z`. -/
def φ {Z : C} (f : morph_components X n Z) :
  X _[n+1] ⟶ Z := P_infty.f (n+1) ≫ f.a +
    ∑ (i : fin (n+1)), ((P i).f (n+1) ≫ (X.δ (reverse_fin i).succ) ≫ (f.b (reverse_fin i)))

variables (X n)
/-- the canonical `morph_components` whose associated morphism is the identity
(see `F_id`) thanks to `decomposition_Q n (n+1)` -/
@[simps]
def id : morph_components X n (X _[n+1]) :=
{ a := P_infty.f (n+1),
  b := λ i, X.σ i, }

lemma id_φ : (id X n).φ = 𝟙 _ :=
begin
  simp only [← P_add_Q_f (n+1) (n+1), φ],
  congr' 1,
  { simp only [id, P_infty_f, P_f_idem], },
  { convert (decomposition_Q n (n+1)).symm,
    ext i,
    simpa only [finset.mem_univ, finset.mem_filter, true_and, true_iff] using fin.is_lt i, },
end

variables {X n}

/-- A `morph_components` can be postcomposed with a morphism. -/
@[simps]
def post_comp : morph_components X n Z' :=
{ a := f.a ≫ h,
  b := λ i, f.b i ≫ h }

lemma post_comp_φ : (f.post_comp h).φ = f.φ ≫ h :=
begin
  unfold φ post_comp,
  simp only [add_comp, sum_comp, assoc],
end

/-- A `morph_components` can be precomposed with a morphism of simplicial objects. -/
@[simps]
def pre_comp : morph_components X' n Z :=
{ a := g.app (op [n+1]) ≫ f.a,
  b := λ i, g.app (op [n]) ≫ f.b i }

lemma pre_comp_φ : (f.pre_comp g).φ = g.app (op [n+1]) ≫ f.φ :=
begin
  unfold φ pre_comp,
  simp only [P_infty_f, comp_add],
  congr' 1,
  { simp only [P_f_naturality_assoc], },
  { simp only [comp_sum, P_f_naturality_assoc, simplicial_object.naturality_δ_assoc], }
end

end morph_components

end dold_kan

end algebraic_topology
