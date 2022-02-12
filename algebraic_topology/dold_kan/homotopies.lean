/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.alternating_face_map_complex
import algebra.homology.homotopy

open category_theory
open category_theory.limits
open category_theory.preadditive
open homotopy
open category_theory.simplicial_object
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

notation `K[`X`]` := alternating_face_map_complex.obj X

/-- As we are using chain complexes indexed by ℕ, we shall need the relation
`c` such `c m n` if and only if `m=n+1`. -/
def c := complex_shape.down ℕ
lemma cs_down_succ (j : ℕ) : (complex_shape.down ℕ).rel (j+1) j := homotopy.cs_down_succ j
lemma cs_down_0_not_rel_left (j : ℕ) : ¬(complex_shape.down ℕ).rel 0 j := homotopy.cs_down_0_not_rel_left j

/-- the sequence of maps that provide the null homotopic map that is used in
the inductive construction of projectors `P q` -/
def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] :=
if n<q
  then 0
  else (-1 : ℤ)^(n-q) • X.σ ⟨n-q, nat.sub_lt_succ n q⟩

/-- We can turn `hσ` into a `prehomotopy`. However, this requires using
`eq_to_hom`. -/
def hσ' (q : ℕ) : prehomotopy K[X] K[X] := λ ij,
(hσ q ij.val.1) ≫ eq_to_hom (by { congr', exact ij.property, })

lemma hσ'_eq_zero {q n m : ℕ} (hnq : n<q) (hnm : c.rel m n) :
  (hσ' q ⟨⟨n, m⟩, hnm⟩ : X _[n] ⟶ X _[m])= 0 :=
begin
  simp only [hσ', hσ],
  split_ifs,
  exact zero_comp,
end

lemma hσ'_eq {q n a m : ℕ} (ha : n=a+q) (hnm : c.rel m n) :
  (hσ' q ⟨⟨n,m⟩,hnm⟩ : X _[n] ⟶ X _[m]) =
  ((-1 : ℤ)^a • X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm ha))⟩) ≫
      eq_to_hom (by { congr', }) :=
begin
  simp only [hσ', hσ],
  split_ifs,
  { exfalso, linarith, },
  { congr; exact tsub_eq_of_eq_add ha, }
end

/-- the null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def Hσ (q : ℕ) : K[X] ⟶ K[X] := homotopy.null_homotopic_map (hσ' q)

/-- `Hσ` is null homotopic -/
def homotopy_Hσ_to_zero (q : ℕ) (X): homotopy (Hσ q :(alternating_face_map_complex C).obj X ⟶ _) 0 :=
homotopy.null_homotopy (hσ' q)

lemma Hσ_eq_zero (q : ℕ) : (Hσ q : K[X] ⟶ _).f 0 = 0  :=
begin
  unfold Hσ,
  rw null_homotopic_map_f_of_not_rel_left (cs_down_succ 0) cs_down_0_not_rel_left,
  cases q,
  { rw hσ'_eq (show 0=0+0, by refl) (cs_down_succ 0),
    simp only [hσ'_eq (show 0=0+0, by refl) (cs_down_succ 0),
      pow_zero, fin.mk_zero, one_zsmul, eq_to_hom_refl, category.comp_id],
    erw chain_complex.of_d,
    simp only [alternating_face_map_complex.obj_d, fin.sum_univ_two,
      fin.coe_zero, pow_zero, one_zsmul, fin.coe_one, pow_one, comp_add,
      neg_smul, one_zsmul, comp_neg, add_neg_eq_zero],
      erw [δ_comp_σ_self, δ_comp_σ_succ], },
  { rw [hσ'_eq_zero (nat.succ_pos q) (cs_down_succ 0), zero_comp], },
end

end dold_kan

end algebraic_topology
