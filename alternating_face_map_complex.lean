/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import algebraic_topology.Moore_complex
import category_theory.abelian.basic
import algebra.big_operators.basic
import tactic.ring_exp

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

We also construct the natural transformation
`inclusion_of_Moore_complex : normalized_Moore_complex A ⟶ alternating_face_map_complex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/

open category_theory category_theory.limits category_theory.subobject
open opposite
open_locale big_operators
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace alternating_face_map_complex

/-!
## Construction of the alternating face map complex
-/

/-- In degree n, the alternating face map complex is given by
the nth-object of the simplicial object -/
@[simp]
def obj_X {C : Type*} [category C] (X : simplicial_object C) (n : ℕ) :=
X.obj (op [n])

variables {C : Type*} [category C] [preadditive C]
variables (X : simplicial_object C)
variables (Y : simplicial_object C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
def obj_d (n : ℕ) : obj_X X (n+1) ⟶ obj_X X n :=
∑ i in finset.range (n+2), (-1 : ℤ)^i • X.δ i

/-!
## Proof of the chain complex relation `d ≫ d`
-/

/-- εdi_dj n (i,j) is the composite `(-1)^j d_j ≫ (-1)^i d_i` -/
def εdi_dj (n : ℕ) (x : ℕ × ℕ) : (obj_X X (n+2)) ⟶ (obj_X X n) :=
((-1 : ℤ)^x.2 • X.δ x.2) ≫ ((-1 : ℤ)^x.1 • X.δ x.1)

lemma εdi_dj_antisymm (n i j : ℕ) (hij : j≤i) (hin : i≤n+1) :
  εdi_dj X n (i,j) = - (εdi_dj X n (j,i+1)) :=
begin
  repeat { rw εdi_dj },
  simp only,
  repeat { rw category_theory.preadditive.comp_zsmul },
  repeat { rw category_theory.preadditive.zsmul_comp },
  rw [← neg_smul, ← mul_smul, ← mul_smul],
  have eq : ((-1)^i * (-1)^j : ℤ) = -(-1)^j * (-1)^(i+1) := by ring_exp,
  rw [← eq],
  apply congr_arg,
  /- the equality shall follow from simplicial identities -/
  have ineq : (j : fin(n+2)) ≤ i,
  { rw ← fin.coe_fin_le,
    rw fin.coe_coe_of_lt (show i<n+2, by linarith),
    rw fin.coe_coe_of_lt (show j<n+2, by linarith),
    exact hij, },
  have hj : fin.cast_succ (j : fin(n+2)) = (j : fin(n+3)),
  { ext,
    rw fin.coe_cast_succ,
    rw fin.coe_coe_of_lt (show j<n+2, by linarith),
    rw fin.coe_coe_of_lt (show j<n+3, by linarith), },
  have hi : (i : fin(n+2)).succ = ((i+1) : ℕ),
  { ext,
    rw fin.coe_succ,
    rw fin.coe_coe_of_lt (show i+1<n+3, by linarith),
    rw fin.coe_coe_of_lt (show i<n+2, by linarith), },
  have seq := category_theory.simplicial_object.δ_comp_δ X ineq,
  rw [hi, hj] at seq,
  rw ← seq,
end

lemma d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
begin
  /- we start by expanding d ≫ d as a double sum -/
  repeat { rw obj_d },
  rw preadditive.comp_sum,
  let d_l := (λ (j:ℕ), (-1 : ℤ)^j • X.δ (j : fin(n+3))),
  let d_r := (λ (i:ℕ), (-1 : ℤ)^i • X.δ (i : fin(n+2))),
  rw [show (λ i, (∑ j in finset.range(n+3), d_l j) ≫ d_r i) =
    (λ i, ∑ j in finset.range(n+3), εdi_dj X n (i,j)),
    by { ext, rw preadditive.sum_comp, refl }],
  rw ← finset.sum_product',
  simp only [prod.mk.eta],
  clear d_l d_r,
  /- then, we split the index set into two parts -/ 
  let s := finset.product (finset.range(n+2)) (finset.range(n+3)),
  let s₁ := finset.filter (λ (x : ℕ × ℕ), x.1<x.2) s,
  rw [← show ∑ x in s \ s₁, εdi_dj X n x + ∑ x in s₁, εdi_dj X n x =
    ∑ x in s, εdi_dj X n x, by { rw finset.sum_sdiff, apply finset.filter_subset, }],
  rw [← eq_neg_iff_add_eq_zero, ← finset.sum_neg_distrib],
  /- we have to show the following map φ induces a bijection s \ s₁ -> s₁ -/
  let φ : ℕ × ℕ → ℕ × ℕ := λ x , (x.2, x.1+1),
  refine (finset.sum_bij (λ x _, φ x) _ _ _ _),
  { intros x hx,
    simp only [finset.mem_sdiff, finset.mem_filter,
      finset.mem_product, finset.mem_range] at hx ⊢,
    rcases hx with ⟨⟨h1a, h1b⟩, h2⟩,
    rw [not_and, and_imp] at h2,
    have h3 := h2 h1a h1b,
    split,
    { split; linarith, },
    { linarith, }, },
  /- the actual antisymmetry relation was proved in lemma εdi_dj_antisymm -/
  { intros x hx,
    simp only [finset.mem_sdiff, finset.mem_filter, finset.mem_product,
      finset.mem_range] at hx,
    rcases hx with ⟨⟨h1a, h1b⟩, h2⟩,
    rw [not_and, and_imp] at h2,
    have h3 := h2 h1a h1b,
    erw εdi_dj_antisymm X n x.1 x.2 (by linarith) (by linarith), },
  /- injectivity of φ -/
  { intros x y hx hx h,
    rw prod.mk.inj_iff at h,
    ext; linarith, },
  /- surjectivity of φ : s \ s₁ -> s₁ -/
  { rintros ⟨y₁, y₂⟩ h1,
    simp only [finset.mem_filter, finset.mem_product, finset.mem_range] at h1,
    cases y₂,
    { exfalso, linarith, },
    { use (y₂,y₁),
      split,
      { simp only [finset.mem_sdiff, finset.mem_filter],
        have h2a := nat.le_of_lt_succ h1.right,
        have h2b := h1.left.right,
        rw nat.succ_eq_one_add at h2b,
        split,
        { simp only [finset.mem_filter, finset.mem_product, finset.mem_range],
          split; linarith, },
        { intro h3, linarith, }, },
      { ext; simp only, }, }, },
end

/-!
## Construction of the alternating face map complex functor
-/

/-- The alternating face map complex, on objects -/
def obj : chain_complex C ℕ := chain_complex.of (obj_X X) (obj_d X) (d_squared X)

variables {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, f.app (op [n]))
  (λ n,
    begin
      repeat { rw obj_d },
      rw [preadditive.comp_sum, preadditive.sum_comp],
      apply congr_arg (finset.range(n+2)).sum,
      ext,
      rw category_theory.preadditive.comp_zsmul,
      rw category_theory.preadditive.zsmul_comp,
      apply congr_arg,
      erw f.naturality,
      refl,
    end)

end alternating_face_map_complex

variables (C : Type*) [category C] [preadditive C]

/-- The alternating face map complex, as a functor -/
@[simps]
def alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := alternating_face_map_complex.obj,
  map := λ X Y f, alternating_face_map_complex.map f }

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/

variables {A : Type*} [category A] [abelian A]

/-- The inclusion map of the Moore complex in the alternating face map complex -/
def inclusion_of_Moore_complex_map (X : simplicial_object A) :
  (normalized_Moore_complex A).obj X ⟶ (alternating_face_map_complex A).obj X :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, (normalized_Moore_complex.obj_X X n).arrow)
  (λ n,
    begin
      /- we have to show the compatibility of the differentials on the alternating
         face map complex with those defined on the normalized Moore complex:
         we first get rid of the terms of the alternating sum that are obviously
         zero on the normalized_Moore_complex -/
      simp only [alternating_face_map_complex.obj_d],
      rw preadditive.comp_sum,
      let t := λ (j : ℕ), (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^j • X.δ j),
      have def_t : (∀ j, t j = (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^j • X.δ j)) := by { intro j, refl, },
      have h := finset.sum_range_add t 1 (n+1),
      rw finset.sum_range_one at h,
      have null : (∀ j, j ∈ finset.range(n+1) → t (1+j) = 0),
      { intros j hj,
        simp only [finset.mem_range] at hj,
        rw def_t,
        rw preadditive.comp_zsmul,
        rw ← zsmul_zero ((-1 : ℤ)^(1+j)),
        apply congr_arg,
        rw normalized_Moore_complex.obj_X,
        rw [show ((1+j : ℕ) : (fin(n+2))) = (j : fin(n+1)).succ, by
          { ext,
            rw fin.coe_succ,
            rw fin.coe_coe_of_lt (show j<n+1, by linarith),
            rw fin.coe_coe_of_lt (show 1+j<n+2, by linarith),
            rw add_comm, }],
        rw ← factor_thru_arrow _ _
          (finset_inf_arrow_factors finset.univ _ (j : fin(n+1)) (by simp)),
        slice_lhs 2 3 { erw kernel_subobject_arrow_comp (X.δ (j:fin(n+1)).succ), },
        simp, },
      rw finset.sum_eq_zero null at h,
      rw [show 1+(n+1)=n+2, by linarith] at h,
      rw h,
      simp only [add_zero],

      /- finally, we study the remaining term which is induced by X.δ 0 -/
      let eq := def_t 0,
      rw [show (-1 : ℤ)^0 = 1, by ring] at eq,
      rw one_smul at eq,
      rw eq,
      clear eq null def_t h t,
      cases n; dsimp; simp,
    end)

@[simp]
lemma inclusion_of_Moore_complex_map_f (X : simplicial_object A) (n : ℕ) :
  (inclusion_of_Moore_complex_map X).f n = (normalized_Moore_complex.obj_X X n).arrow :=
chain_complex.of_hom_f _ _ _ _ _ _ _ _ n

variables (A)

/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
def inclusion_of_Moore_complex :
  nat_trans (normalized_Moore_complex A) (alternating_face_map_complex A) :=
{ app := inclusion_of_Moore_complex_map, }

end algebraic_topology

