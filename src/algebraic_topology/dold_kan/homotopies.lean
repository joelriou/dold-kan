/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

--import for_mathlib.homotopy
import algebra.homology.homotopy
import for_mathlib.homotopy_var
import for_mathlib.functor_misc
import algebraic_topology.dold_kan.notations

/- TODO doc : provide some details about the operators `P q` -/

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.preadditive
open category_theory.simplicial_object
open homotopy
open opposite
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

universe v

variables {C : Type*} [category.{v} C] [preadditive C]
variables {X : simplicial_object C}

/-- As we are using chain complexes indexed by ℕ, we shall need the relation
`c` such `c m n` if and only if `m=n+1`. -/
@[simp]
def c := complex_shape.down ℕ

def c_mk (i j : ℕ) (h : j+1 = i) : (complex_shape.down ℕ).rel i j := h

lemma cs_down_succ (j : ℕ) : c.rel (j+1) j := by { dsimp, refl, }

lemma cs_down_0_not_rel_left (j : ℕ) : ¬c.rel 0 j :=
begin
  intro hj,
  dsimp at hj,
  apply nat.not_succ_le_zero j,
  rw [nat.succ_eq_add_one, hj],
end

/-- the sequence of maps that provide the null homotopic map that is used in
the inductive construction of projectors `P q` -/
def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] :=
if n<q
  then 0
  else (-1 : ℤ)^(n-q) • X.σ ⟨n-q, nat.sub_lt_succ n q⟩

/-- We can turn `hσ` into a `prehomotopy`. However, this requires using
`eq_to_hom`. -/
def hσ' (q : ℕ) : Π i j, c.rel j i → (K[X].X i ⟶ K[X].X j) :=
λ i j hij, (hσ q i) ≫ eq_to_hom (by congr')

lemma hσ'_eq_zero {q n m : ℕ} (hnq : n<q) (hnm : c.rel m n) :
  (hσ' q n m hnm : X _[n] ⟶ X _[m])= 0 :=
begin
  simp only [hσ', hσ],
  split_ifs,
  exact zero_comp,
end

lemma hσ'_eq {q n a m : ℕ} (ha : n=a+q) (hnm : c.rel m n) :
  (hσ' q n m hnm : X _[n] ⟶ X _[m]) =
  ((-1 : ℤ)^a • X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm ha))⟩) ≫
      eq_to_hom (by { congr', }) :=
begin
  simp only [hσ', hσ],
  split_ifs,
  { exfalso, linarith, },
  { congr; exact tsub_eq_of_eq_add ha, }
end

/-- the null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def Hσ (q : ℕ) : K[X] ⟶ K[X] := homotopy.null_homotopic_map' (hσ' q)

variable (X)

/-- `Hσ` is null homotopic -/
def homotopy_Hσ_to_zero (q : ℕ) : homotopy (Hσ q : K[X] ⟶ K[X]) 0 :=
homotopy.null_homotopy' (hσ' q)

variable {X}
lemma Hσ_eq_zero (q : ℕ) : (Hσ q : K[X] ⟶ K[X]).f 0 = 0  :=
begin
  unfold Hσ,
  rw null_homotopic_map'_f_of_not_rel_left (cs_down_succ 0) cs_down_0_not_rel_left,
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

lemma hσ_naturality (q n : ℕ) {X Y : simplicial_object C} (f : X ⟶ Y) :
  (f.app (op [n]) ≫ hσ q n : X _[n] ⟶ Y _[n+1]) =
  hσ q n ≫ f.app (op [n+1]) :=
begin
  by_cases hqn : n<q; unfold hσ; split_ifs,
  { simp only [zero_comp, comp_zero], },
  { simp only [zsmul_comp, comp_zsmul],
    congr' 1,
    erw f.naturality,
    refl, },
end

lemma hσ'_naturality (q : ℕ) (i j : ℕ) (hij : c.rel j i)
  {X Y : simplicial_object C} (f : X ⟶ Y) :
  f.app (op [i]) ≫ hσ' q i j hij = hσ' q i j hij ≫ f.app (op [j]) :=
begin
  dsimp [c] at hij,
  have h : i+1 = j := hij,
  subst h,
  simp only [hσ', hσ_naturality, eq_to_hom_refl, comp_id],
end

/-- For each q, Hσ q is a natural transformation. -/
def nat_trans_Hσ (q : ℕ) :
  alternating_face_map_complex C ⟶ alternating_face_map_complex C :=
{ app := λ _, Hσ q,
  naturality' := λ X Y f, begin
    unfold Hσ,
    rw [null_homotopic_map'_comp, comp_null_homotopic_map'],
    congr,
    ext i j hij,
    simp only [alternating_face_map_complex_map, alternating_face_map_complex.map,
      chain_complex.of_hom_f, hσ'_naturality],
  end }

lemma map_hσ' {D : Type*} [category.{v} D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C)
  (q i j : ℕ) (hij : c.rel j i) :
  (hσ' q i j hij : K[((whiskering _ _).obj G).obj X].X i ⟶ _) =
  G.map (hσ' q i j hij : K[X].X i ⟶ _) :=
begin
  unfold hσ' hσ,
  split_ifs,
  { simp only [functor.map_zero, zero_comp], },
  { simpa only [eq_to_hom_map, functor.map_comp, functor.map_zsmul], },
end

lemma map_Hσ {D : Type*} [category.{v} D] [preadditive D]
  (G : C ⥤ D) [G.additive] (X : simplicial_object C) (q n : ℕ) :
  (Hσ q : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
  G.map ((Hσ q : K[X] ⟶ _).f n) :=
begin
  unfold Hσ,
  have eq := homological_complex.congr_hom (map_null_homotopic_map' G (hσ' q)) n,
  dsimp [functor.map_homological_complex] at eq,
  simp only [← map_hσ'] at eq,
  erw eq,
  let h := (congr_obj (map_alternating_face_map_complex G) X).symm,
  congr',
end

end dold_kan

end algebraic_topology
