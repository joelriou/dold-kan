/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import algebraic_topology.Moore_complex
import category_theory.abelian.basic
import algebra.big_operators.basic

/-!

# The alternating face map complex of a simplicial object in a abelian category

We construct the alternating face map complex, as a 
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any abelian category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternate sums of faces.

We also construct the natural transformation 
`inclusion_of_Moore_complex : nat_trans (normalized_Moore_complex C) (alternating_face_map_complex C)` 


## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/

open category_theory category_theory.limits category_theory.subobject
open opposite
open_locale big_operators

noncomputable theory
namespace algebraic_topology

variables {C : Type*} [category C] [abelian C]
variables (X : simplicial_object C)
variables (Y : simplicial_object C)

namespace alternating_face_map_complex

@[simp]
def obj_X (n : ℕ) := X.obj(op(simplex_category.mk n))

@[simp]
def obj_d (n : ℕ) : (obj_X X (n+1) ⟶ (obj_X X n)) :=
∑ i in finset.range (n+2), ((-1 : ℤ)^i • X.δ i)

/-!
## Proof of the relation chain complex relation `d ≫ d` 

The expansion of `d ≫ d` involves a double sum, or a sum of terms
indexed by a set of the form {0,...,n} × {0,...,n+1}. We shall show
a general cancellation lemma `antisymmetric_sum_cancels` of such sums when
the terms f_{i,j} satisfy an "antisymmetry" relation f_{i,j+1}=-t_{j,i}
for i≤j, The cancellation lemma follows from the study of a certain
involution `τ` on `ℕ × ℕ`.

### Definition of an involution `τ : ℕ × ℕ → ℕ × ℕ`

-/

/--
We split elements `ℕ × ℕ` into two cases. "Case 1" is the situation of
tuples `(i,j)` such that `i<j`, and "Case 2" is the other situation. These
two subsets are exchanged by τ
-/
def τ (x : ℕ × ℕ ) : ℕ × ℕ :=
if x.1 < x.2
  then (x.2-1,x.1)
  else (x.2,x.1+1)

lemma τ_case1 (x : ℕ × ℕ) (hx : (x.1<x.2)) : τ x = (x.2-1,x.1) :=
by { rw τ, split_ifs, refl }

lemma τ_case2 (x : ℕ × ℕ) (hx : ¬x.1<x.2) : τ x = (x.2,x.1+1) :=
by { rw τ, split_ifs, refl }

/-!
### Verification that τ induces an involution τ' on {0,...,n} × {0,...,n+1}

`indices n` denotes `{0,...,n} × {0,...,n+1}` as a finite subset of `ℕ × ℕ`

-/

def indices (n : ℕ) : finset (ℕ × ℕ) := 
finset.product (finset.range(n+1)) (finset.range(n+2))

def τ' {n : ℕ} : (Π (x : ℕ × ℕ), x ∈ (indices n) → (ℕ × ℕ)) := 
λ x hx, τ x

@[simp] lemma τ'_eq_τ {n : ℕ} (x : ℕ × ℕ) (hx : x ∈ (indices n)) :
τ' x hx = τ x := by refl

/-- τ stabilises {0,...,n} × {0,...,n+1} -/
lemma τ'_mem {n : ℕ} : (∀ (x : ℕ × ℕ) (hx : x ∈ indices n), τ' x hx ∈ indices n) :=
begin
  intros x hx,
  rw τ'_eq_τ,
  simp only [indices, finset.mem_product, finset.mem_range] at hx,
  cases hx with hx1 hx2,
  by_cases x.1<x.2,
    { rw τ_case1 x h,
      simp only [indices, finset.mem_product, finset.mem_range],
      split,
        { exact nat.pred_lt_pred (show x.2 ≠ 0, by linarith) hx2, },
        { linarith, },
    },
    { rw τ_case2 x h,
      simp only [indices, finset.mem_product, finset.mem_range],
      split; linarith,
    }
end

variables { α : Type* }

/-- τ' has no fixed point -/
lemma τ'_ne [add_comm_monoid α] {n : ℕ} {f : ℕ × ℕ → α} :
  (∀ (x : ℕ × ℕ) (hx : x ∈ indices n), f x ≠ 0 → τ' x hx ≠ x) :=
begin
  intros x hx hfx,
  rw τ'_eq_τ,
  by_cases x.1<x.2,
    { rw τ_case1 x h,
      intro h1,
      have h2 := congr_arg prod.snd h1,
      simp only at h2,
      linarith,
    },
    { rw τ_case2 x h,
      intro h1,
      have h2 := congr_arg prod.fst h1,
      have h3 := congr_arg prod.snd h1,
      simp only at h2 h3,
      linarith,
    }
end

lemma τ_of_case2_is_case1 (x : ℕ × ℕ) (hx : ¬x.1<x.2) : x.2<x.1+1 := by linarith

lemma τ_of_case1_is_case2 (x : ℕ × ℕ) (hx : x.1<x.2) : ¬x.2-1<x.1 :=
begin
  intro h,
  cases x.2,
    { linarith, },
    {
      rw nat.succ_sub_one at h,
      have h1 := nat.le_of_lt_succ hx,
      linarith,
    },
end

/-! τ' is an involution. -/
lemma τ'_inv {n : ℕ} : (∀ (x : ℕ × ℕ) (hx : x ∈ indices n),
  τ' (τ' x hx) (τ'_mem x hx) = x) :=
begin
  intros x hx,
  simp only [τ'_eq_τ],
  by_cases x.1<x.2,
    { rw τ_case1 x h,
      have h1 := τ_case2 (x.2-1,x.1) (τ_of_case1_is_case2 x h),
      simp only at h1,
      rw h1,
      ext; simp only,
        cases x.2 with m,
          { linarith, },
          { exact nat.succ_sub_one m.succ, }
    },
    { rw τ_case2 x h,
      have h1 := τ_case1 (x.2,x.1+1) (τ_of_case2_is_case1 x h),
      simp only at h1,
      rw h1,
      ext; simp only, 
        exact nat.succ_sub_one x.1,
    },
end

/-!
### Cancellation of "antisymmetric" sums indexed by {0,...,n} × {0,...,n+1}
-/

/-- The proof uses finset.sum_involution. Then, from the assumption, we have
to show that for all x in {0,...,n} × {0,...,n+1}, we have `x + f (τ x) = 0`.
-/
lemma antisymmetric_sum_cancels [add_comm_group α] {n : ℕ} (f : ℕ × ℕ → α)
  (antisymmetry_f : ∀ (i j : ℕ), i≤j → j≤n → f (i,j+1) = - f (j,i)) :
  ∑ x in (indices n), f x = 0 :=
begin
  have h0 : (∀ (x : ℕ × ℕ) (hx : x ∈ (indices n)), f x + f (τ' x hx) = 0),
  { intros x hx,
    rw τ'_eq_τ,
    simp only [indices, finset.mem_product, finset.mem_range] at hx,
    cases hx with hx1 hx2,
    by_cases x.1<x.2,
      { rw τ_case1 x h,
        have ineq : x.2-1 ≤ n := nat.pred_le_pred (nat.lt_succ_iff.mp hx2),
        have h1 := antisymmetry_f x.1 (x.2-1) (nat.le_pred_of_lt h) ineq,
        have eq : x.2-1+1 = x.2,
        { cases x.2 with j,
            { exfalso, linarith },
            { exact nat.succ_sub_one j.succ, }
        },
        rw eq at h1,
        simp only [prod.mk.eta] at h1,
        rw h1,
        simp only [add_left_neg],
      },
      { rw τ_case2 x h,
        rw antisymmetry_f x.2 x.1 (by linarith) (by linarith),
        simp only [prod.mk.eta, add_right_neg],
      }
  },
  exact finset.sum_involution τ' h0 τ'_ne τ'_mem τ'_inv ,
end

/-!
### Antisymmetry property for the terms that appear in the expansion of `d ≫ d`
-/

def di_dj (n : ℕ) (x : ℕ × ℕ) : obj_X X (n+2) ⟶ (obj_X X n) :=
  ((-1 : ℤ)^x.2 • X.δ x.2) ≫ ((-1 : ℤ)^x.1 • X.δ x.1)

lemma di_dj_antisymm (n : ℕ) : (∀ (i j : ℕ), i≤j → j≤n+1 →
  (di_dj X n (i,j+1)) = - di_dj X n (j,i)):=
begin
  intros i j hij hjn,
  repeat { rw di_dj },
  simp only,
  repeat { rw category_theory.preadditive.comp_zsmul },
  repeat { rw category_theory.preadditive.zsmul_comp },
  repeat { rw ← mul_smul },
  have eq : -((-1)^i * (-1)^j : ℤ) = (-1)^i * (-1)^(j+1),
  { rw pow_succ,
    rw ← mul_assoc,
    rw mul_comm ((-1 : ℤ)^i) (-1),
    simp only [neg_mul_eq_neg_mul_symm, one_mul],
  },
  rw [← eq, mul_comm , ← neg_smul],
  apply congr_arg,
  have ineq : ( i : fin(n+2)) ≤ j,
  { rw ← fin.coe_fin_le,
    rw fin.coe_coe_of_lt (show i<n+2, by linarith),
    rw fin.coe_coe_of_lt (show j<n+2, by linarith),
    exact hij,
  },
  have hi : fin.cast_succ (i : fin(n+2)) = (i : fin(n+3)),
  { ext,
    rw fin.coe_cast_succ,
    rw fin.coe_coe_of_lt (show i<n+2, by linarith),
    rw fin.coe_coe_of_lt (show i<n+3, by linarith),
  },
  have hj : (j : fin(n+2)).succ = ((j+1) : ℕ),
  { ext,
    rw fin.coe_succ,
    rw fin.coe_coe_of_lt (show j+1<n+3, by linarith),
    rw fin.coe_coe_of_lt (show j<n+2, by linarith),
  },
  have seq := category_theory.simplicial_object.δ_comp_δ X ineq,
  rw [hi, hj] at seq,
  exact seq,
end

/-!
### End of the proof of `d ≫ d = 0`
-/
lemma d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
begin
  repeat { rw obj_d },
  rw preadditive.comp_sum,
  let d_l := (λ (j:ℕ), (-1 : ℤ)^j • X.δ (j : fin(n+3))),
  let d_r := (λ (i:ℕ), (-1 : ℤ)^i • X.δ (i : fin(n+2))),
  rw [show (λ i, (∑ j in finset.range(n+3), d_l j) ≫ d_r i) =
    (λ i, ∑ j in finset.range(n+3), di_dj X n (i,j)),
    by { ext, rw preadditive.sum_comp, refl }],
  rw ← finset.sum_product',
  clear d_l d_r,
  exact antisymmetric_sum_cancels (di_dj X n) (di_dj_antisymm X n),
end

/-!
## Construction of the alternating face map complex functor
-/

def obj : chain_complex C ℕ := chain_complex.of (obj_X X) (obj_d X) (d_squared X)

variables {X} {Y}

@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  chain_complex.of_hom _ _ _ _ _ _
  (λ n, f.app(op(simplex_category.mk n)))
  (λ n,
    begin
      repeat { rw obj_d },
      rw preadditive.comp_sum,
      rw preadditive.sum_comp,
      apply congr_arg (finset.range(n+2)).sum,
      ext,
      rw category_theory.preadditive.comp_zsmul,
      rw category_theory.preadditive.zsmul_comp,
      apply congr_arg,
      erw f.naturality,
      refl,
    end)

end alternating_face_map_complex

variables (C)

@[simps]
def alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := alternating_face_map_complex.obj,
  map := λ X Y f, alternating_face_map_complex.map f
}


/-- A small lemma which may appear somewhere else in mathlib? -/
variables {α : Type*}
lemma smul_zero_var [add_comm_group α] (n : ℤ) (x : α) (hx : x = 0) : n•x = 0 :=
begin
  rw hx,
  simp only [smul_zero'],
end

/-!
## Construction of the natural inclusion from the normalized Moore complex to the alternating face map complex
-/

variables {C}
def inclusion_of_Moore_complex_map (X : simplicial_object C) :  
  (normalized_Moore_complex C).obj X ⟶ (alternating_face_map_complex C).obj X :=
chain_complex.of_hom _ _ _ _ _ _ 
  (λ n, (normalized_Moore_complex.obj_X X n).arrow)
  (λ n,
    begin
      simp only [alternating_face_map_complex.obj_d],
      rw preadditive.comp_sum,
      let t := λ (j : ℕ), (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^j • X.δ j),
      have def_t : (∀ j, t j = (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^j • X.δ j)) := by { intro j, refl, },
      have h := finset.sum_range_add t 1 (n+1),
      rw finset.sum_range_one at h,
      have null : (∀ j, j ∈ finset.range(n+1) → t (1+j) = 0 ),
      { intros j hj,
        simp only [finset.mem_range] at hj,
        rw def_t,
        rw preadditive.comp_zsmul,
        apply smul_zero_var,
        rw normalized_Moore_complex.obj_X,
        rw [show ((1+j : ℕ) : (fin(n+2))) = (j:fin(n+1)).succ, by
          { ext,
            rw fin.coe_succ,
            rw fin.coe_coe_of_lt (show j<n+1, by linarith),
            rw fin.coe_coe_of_lt (show 1+j<n+2, by linarith),
            rw add_comm,
          }],
        rw ← factor_thru_arrow _ _
          (finset_inf_arrow_factors finset.univ _ (j : fin(n+1)) (by simp)),
        slice_lhs 2 3 { erw kernel_subobject_arrow_comp (X.δ (j:fin(n+1)).succ), },
        simp,
      },
      rw finset.sum_eq_zero null at h,
      rw [show 1+(n+1)=n+2, by linarith] at h,
      rw h,
      simp only [add_zero],

      let eq := def_t 0,
      rw [show (-1 : ℤ)^0 = 1, by ring] at eq,
      rw one_smul at eq,
      rw eq,
      clear eq null def_t h t,
      cases n; dsimp; simp,
    end)

@[simp]
lemma inclusion_of_Moore_complex_map_f (X : simplicial_object C) (n : ℕ) :
  (inclusion_of_Moore_complex_map X).f n = (normalized_Moore_complex.obj_X X n).arrow :=
  chain_complex.of_hom_f _ _ _ _ _ _ _ _ n

variables (C)
@[simps]
def inclusion_of_Moore_complex :
  nat_trans (normalized_Moore_complex C) (alternating_face_map_complex C) :=
{ app := inclusion_of_Moore_complex_map, }

end algebraic_topology

