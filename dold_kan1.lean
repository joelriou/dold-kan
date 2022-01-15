/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebra.homology.homotopy
import algebra.big_operators.basic
import algebraic_topology.simplicial_object
import algebraic_topology.alternating_face_map_complex

/-!

# The Dold-Kan correspondence

The Dold-Kan correspondance states that for any abelian category `A`, there is
an equivalence between the category of simplicial objects in `A` and the
category of chain complexes in `A` (with degrees indexed by `ℕ` and the
homological convention that the degree is decreased by the differentials).

More generally, this results holds for pseudo-abelian categories. Taking this
into consideration, the strategy of proof that is used here is to state and
prove most of the technical results without referring to notions of kernel,
images, etc. The core of the arguments shall be constructing morphisms and 
check equalities between morphisms. The applications to abelian categories
are handled at the very end of the proof.

The overall plan is as follows:

* show that the normalized Moore complex is an homotopy equivalent direct factor of
the alternating face map complex, see `P_infty`
and `homotopy_equiv_inclusion_of_Moore_complex`
* show that a morphism of simplicial objects is an isomorphisms if and only if it
induces an isomorphism on normalized Moore complexes
* construct the inverse functor from chain complexes to simplicial objects 
* check that this gives the expected equivalence of categories (TODO)

## References
* Albrecht Dold, Homology of Symmetric Products and Other Functors of Complexes,
Annals of Mathematics, Second Series, Vol. 68 No. 1 (Jul. 1958), pp. 54-80.
* Paul G. Goerss, John F. Jardine, Simplical Homotopy Theory, Modern Birkhäuser Classics,
Reprint of the 1999 edition.

-/

open category_theory
open category_theory.limits
open category_theory.subobject
open category_theory.preadditive
open category_theory.simplicial_object
open category_theory.category
open homology
open opposite

open_locale big_operators
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace dold_kan

/-!
## The normalized Moore complex, as a direct factor of the alternating face map complex

In this section, we construct an endomorphism `P_infty` of the alternating face
map complex of a simplicial object `X`. In the case of abelian cateogies, this
shall be the projector with image the normalized Moore complex and kernel the
subcomplex spanned by degeneracies.

By induction, we first construct a sequence of projectors `P q` for
`(q : ℕ)`. In the abelian category case, the image of `P q` is the subcomplex
which in degree n is given by the intersection of the q higher faces
(excluding `δ 0`) and whose kernel shall be the sum of the images of the q
higher degeneracies (also excluding `sigma q`). By construction, they are all
homotopic to the identity, in degreewise, `P q` is eventually constant, which will
make the construction of `P_infty` possible.

-/

variables {C : Type*} [category C] [preadditive C]

variables {X : simplicial_object C}

/-- As we are using chain complexes indexed by ℕ, we shall need the relation
`c` such `c m n` if and only if `m=n+1`. -/
def c := complex_shape.down ℕ
/-! Restatement of `homotopy.cs_down_succ` and `homotopy.cs_down_0_not_rel_left`,
  which avoids opening `homotopy`. -/
lemma cs_down_succ (j : ℕ) : (complex_shape.down ℕ).rel (j+1) j := homotopy.cs_down_succ j
lemma cs_down_0_not_rel_left (j : ℕ) : ¬(complex_shape.down ℕ).rel 0 j := homotopy.cs_down_0_not_rel_left j

/-- the sequence of maps that provide the null homotopic map that is used in
the inductive construction of projectors `P q` -/
def hσ (q : ℕ) (n : ℕ) : X _[n] ⟶ X _[n+1] := if n<q then 0
  else (-1 : ℤ)^(n-q) • X.σ ⟨n-q, nat.sub_lt_succ n q⟩

/-- We can turn `hσ` into a `prehomotopy`. However, this requires using
`eq_to_hom`. -/
def hσ' (q : ℕ) : prehomotopy ((alternating_face_map_complex C).obj X)
  ((alternating_face_map_complex C).obj X) := λ ij,
(hσ q ij.val.1) ≫ eq_to_hom (by { congr', exact ij.property, })
  
/-- the null homotopic map $(hσ q) ∘ d + d ∘ (hσ q)$ -/
def Hσ (q : ℕ) : (alternating_face_map_complex C).obj X ⟶
  (alternating_face_map_complex C).obj X := homotopy.null_homotopic_map (hσ' q)

/-- `Hσ` is null homotopic -/
def homotopy_Hσ_to_zero (q : ℕ) (X): homotopy (Hσ q :(alternating_face_map_complex C).obj X ⟶ _) 0 :=
homotopy.null_homotopy (hσ' q)

lemma hσ'_eq_zero {q n m : ℕ} (hnq : n<q) (hnm : c.rel m n) : (hσ' q ⟨⟨n,m⟩,hnm⟩ : X _[n] ⟶ X _[m])= 0 :=
begin
  simp only [hσ', hσ],
  split_ifs,
  exact zero_comp,
end

lemma hσ'_eq {q n a m : ℕ} (ha : n=a+q) (hnm : c.rel m n) : (hσ' q ⟨⟨n,m⟩,hnm⟩ : X _[n] ⟶ X _[m]) =
    ((-1 : ℤ)^a • X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm ha))⟩) ≫
      eq_to_hom (by { congr', }) :=
begin
  simp only [hσ', hσ],
  split_ifs,
  { exfalso, linarith, },
  { congr; exact tsub_eq_of_eq_add ha, }
end


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
noncomputable def P : ℕ → ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X)
| 0     := 𝟙 _
| (q+1) := P q ≫ (𝟙 _ + Hσ q)

/- All the `P q` coincide with `𝟙` in degree 0. -/
lemma P_deg0_eq (q : ℕ) : ((P q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
begin
  induction q with q hq,
  { simp only [homological_complex.id_f, P], },
  { unfold P,
    simp only [homological_complex.comp_f, homological_complex.add_f_apply,
      homological_complex.id_f, hq, comp_add, id_comp, add_right_eq_self,
      Hσ, homotopy.null_homotopic_map_f_of_not_rel_left
        (cs_down_succ 0) cs_down_0_not_rel_left],
    cases q, swap, rw [hσ'_eq_zero (nat.succ_pos q) (cs_down_succ 0), zero_comp],
    simp only [hσ'_eq (show 0=0+0, by refl) (cs_down_succ 0)],
    simp only [fin.mk_zero, one_zsmul, eq_to_hom_refl, comp_id, pow_zero],
    erw chain_complex.of_d, simp [alternating_face_map_complex.obj_d],
    simp only [fin.sum_univ_two, comp_neg, fin.coe_zero, comp_add, fin.coe_one,
      pow_one, one_zsmul, pow_zero, neg_smul],
    apply add_neg_eq_zero.mpr,
    erw [δ_comp_σ_self, δ_comp_σ_succ], }
end

/-- As we want to construct projectors `P q` which, in the abelian category case,
factors through the kernel of some of differentials, we introduce this
`structure higher_faces_vanish` which expresses that a certain map
`φ : Y ⟶ X _[n+1]` is such that `φ ≫ X.δ i` for the q biggest possible indices
`i`, excluding 0.
-/
structure higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
  (vanishing : ∀ (j : fin (n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0)

/-- the map `λ a, a+i` from `fin` q to `fin n`, when $n=a+q$ -/
@[simp]
def translate_fin {n : ℕ} (a : ℕ) {q : ℕ} (hnaq : n=a+q) (i : fin q) : fin n :=
⟨a+(i:ℕ), (gt_of_ge_of_gt (eq.ge hnaq) ((add_lt_add_iff_left a).mpr (fin.is_lt i)))⟩

lemma remove_trailing_zeros_in_sum {β : Type*} [add_comm_monoid β] {n a q : ℕ}
  (hnaq : n=a+q) (f : fin(n) → β)
  (hf : ∀ (j : fin(q)), f (translate_fin a hnaq j) = 0) :
  ∑ (i : fin(n)), f i =
  ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ, f i := 
begin
  let lt_a := λ (i : fin(n)), (i:ℕ)<a,
  have vanishing : ∀ (i : fin(n)), i ∈ (finset.univ : finset(fin(n))) → f i ≠ 0 → lt_a i,
  { intros i hi0,
    by_cases hi1 : lt_a i,
    { intro, assumption, },
    { intro hi2,
      exfalso,
      simp only [not_lt] at hi1,
      cases nat.le.dest hi1 with j hj,
      have hjq : j<q,
      { apply (add_lt_add_iff_left a).mp,
        rw [← hnaq, hj],
        exact fin.is_lt i, },
      have hfj := hf ⟨j, hjq⟩,
      simp only [hj, translate_fin, fin.eta, fin.coe_mk] at hfj,
      exact hi2 hfj, }, },
  simp only [← finset.sum_filter_of_ne vanishing],
end

lemma leave_out_last_term {β : Type*} [add_comm_monoid β] {n a : ℕ} (hna : a<n)
  {f : fin(n) → β} :
  ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a+1) finset.univ, f i = 
  ∑ (i : fin(n)) in finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ, f i + f ⟨a, hna⟩ :=
begin
  conv { to_rhs, rw add_comm, },
  let S := finset.filter (λ i : fin(n), (i:ℕ)<a) finset.univ,
  let b : fin (n) := ⟨a, hna⟩,
  rw ← finset.sum_insert (_ : b ∉ S), swap,
  { simp only [lt_self_iff_false, not_false_iff, finset.mem_filter, fin.coe_mk, and_false], },
  congr',
  ext i,
  simp only [true_and, finset.mem_univ, finset.mem_insert, finset.mem_filter],
  simp only [nat.lt_iff_add_one_le],
  rw [nat.le_add_one_iff],
  conv { to_lhs, congr, skip, rw [add_left_inj 1], },
  conv { to_rhs, rw or.comm, congr, skip, rw [fin.ext_iff, fin.coe_mk], },
end

lemma Hσφ_eq_neg_σδ {Y : C} {n a q : ℕ} (hnaq : n=a+q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 
  - φ ≫ X.δ ⟨a+1, nat.succ_lt_succ (nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq)))⟩ ≫
  X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq))⟩ :=
begin
  have hnaq_shift : Π d : ℕ, n+d=(a+d)+q,
  { intro d, rw [add_assoc, add_comm d, ← add_assoc, hnaq], },
  simp only [Hσ],
  rw [homotopy.null_homotopic_map_f (cs_down_succ (n+1)) (cs_down_succ n),
    hσ'_eq hnaq (cs_down_succ n), hσ'_eq (hnaq_shift 1) (cs_down_succ (n+1))],
  repeat { erw chain_complex.of_d, },
  simp only [alternating_face_map_complex.obj_d, eq_to_hom_refl, comp_id],
  simp only [comp_sum, sum_comp, comp_id, comp_add],
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul],
  have ineq1 : a<n+1 := nat.lt_succ_iff.mpr (nat.le.intro (eq.symm hnaq)),
  have ineq2 : a+1< n+2 := nat.succ_lt_succ ineq1,
  let term1 := λ (j : fin (n+2)), ((-1 : ℤ)^(j : ℕ) * (-1 : ℤ)^a) • (φ ≫ X.δ j) ≫ X.σ ⟨a, ineq1⟩,
  let term2 := λ (j : fin (n+3)), ((-1 : ℤ)^(a+1) * (-1 : ℤ)^(j : ℕ)) • (φ ≫ X.σ ⟨a+1, ineq2⟩) ≫ X.δ j,
  let j : fin(n+1) := ⟨n-q, nat.sub_lt_succ n q⟩,
  simp only [← term1, ← term2],
  /- cleaning up the first sum -/
  rw remove_trailing_zeros_in_sum (hnaq_shift 2) term1, swap,
  { intro k,
    simp only [term1],
    have hk := fin.is_lt k,
    let i : fin (n+1) := ⟨a+k+1, by linarith⟩,
    have eq := v.vanishing i (by { simp only [i, fin.coe_mk], linarith, }),
    have hi : translate_fin (a+2) (hnaq_shift 2) k = i.succ,
    { ext, simp only [fin.succ_mk, translate_fin, fin.coe_mk], linarith, },
    rw [hi, eq],
    simp only [smul_zero', zero_comp], },
  /- cleaning up the second sum -/
  rw remove_trailing_zeros_in_sum (hnaq_shift 3) term2, swap,
  { intro k,
    simp only [term2],
    have hk := fin.is_lt k,
    let i : fin(n+1) := ⟨a+1+(k : ℕ), by linarith⟩,
    have hia : fin.cast_succ (⟨a+1, by linarith⟩ : fin(n+1)) < i.succ,
    { simp only [fin.lt_iff_coe_lt_coe, fin.succ_mk, fin.cast_succ_mk,
        add_lt_add_iff_right, fin.coe_mk],
      linarith, },
    have δσ_rel := δ_comp_σ_of_gt X hia,
    have hisucc : i.succ.succ = translate_fin (a+3) (hnaq_shift 3) k,
    { ext, simp only [fin.succ_mk, translate_fin, fin.coe_mk], linarith, },
    rw [hisucc, fin.cast_succ_mk] at δσ_rel,
    rw [assoc, δσ_rel],
    have eq := v.vanishing i (by { simp only [i, fin.coe_mk], linarith, }),
    rw [← assoc, eq],
    simp only [smul_zero', zero_comp], },
  /- leaving out three terms -/
  rw [leave_out_last_term (ineq2 : a+1<n+2),
    leave_out_last_term (show a+2<n+3, by linarith),
    leave_out_last_term (show a+1<n+3, by linarith)],
  /- the purpose of the following lemma is to create three subgoals in order
    to finish the proof -/
  have simplif : ∀ (a b c d e f : Y ⟶ X _[n+1]), b=f → d+e=0 → c+a=0 → a+b+(c+d+e) =f,
  { intros a b c d e f h1 h2 h3,
    rw [add_assoc c d e, h2, add_zero, add_comm a b, add_assoc,
      add_comm a c, h3, add_zero, h1], },
  apply simplif,
  { /- b=f -/
    simp only [term1],
    rw fin.coe_mk,
    have eq : (-1 : ℤ)^(a+1) * (-1 : ℤ)^a = -1,
    { calc (-1 : ℤ)^(a+1)*(-1 : ℤ)^a  = - ((-1 : ℤ)^a*(-1 : ℤ)^a) : by ring_exp
      ...                             = - ((-1 : ℤ)*(-1 : ℤ))^a : by rw ← mul_pow
      ...                             = - 1^a : by ring
      ...                             = - 1   : by ring_exp },
    rw [eq, neg_smul, one_zsmul, assoc], },
  { /- d+e=0 -/
    simp only [term2],
    let b : fin(n+2) := ⟨a+1, ineq2⟩,
    have eq1 : X.σ b ≫ X.δ (fin.cast_succ b) = 𝟙 _ := by rw δ_comp_σ_self,
    have eq2 : X.σ b ≫ X.δ b.succ = 𝟙 _ := by rw δ_comp_σ_succ,
    simp only [b, fin.cast_succ_mk, fin.succ_mk] at eq1 eq2,
    rw [assoc, assoc, eq1, eq2],
    simp only [comp_id, fin.coe_mk],
    apply add_eq_zero_iff_eq_neg.mpr,
    have eq3 : (-1 : ℤ)^(a+2) = (-1 : ℤ) * (-1 : ℤ)^(a+1),
    { have eq4 := pow_add (-1 : ℤ) 1 (a+1),
      rw pow_one at eq4,
      congr' 1, },
    simp only [eq3, neg_mul_eq_neg_mul_symm, one_mul,
      mul_neg_eq_neg_mul_symm, neg_neg, neg_smul], },
  { /- c+a=0 -/
    let ι : fin (n+2) → fin (n+3) := fin.cast_succ,
    let S := finset.filter (λ i : fin(n+2), (i:ℕ)<a+1) finset.univ,
    let T := finset.filter (λ i : fin(n+3), (i:ℕ)<a+1) finset.univ,
    have eq : ∑ (s : fin(n+2)) in S, term2 (ι s) =
              ∑ (t : fin(n+3)) in T, term2 t    := finset.sum_bij (λ (s : fin(n+2))
      (hs : s ∈ finset.filter (λ i : fin(n+2), (i:ℕ)<a+1) finset.univ), ι s) _ _ _ _, rotate,
    /- we check that we have a bijection between S:= {0,...,a} as a subset of fin(n+2)
      and T := {0,...,a} as a subset of fin(n+3) -/
      { intros a ha,
        simp only [true_and, finset.mem_univ, fin.coe_cast_succ,
          finset.mem_filter] at ha ⊢,
        assumption, },
      { intros a ha, refl, },
      { intros a b ha hb H,
        simp only [order_embedding.eq_iff_eq] at H,
        rw H, },
      { intros b hb,
        simp only [true_and, finset.mem_univ, fin.coe_cast_succ,
          finset.mem_filter] at hb,
        have hb2 : (b:ℕ) < n+2 := by linarith,
        use (⟨(b : ℕ), hb2⟩ : fin(n+2)),
        split,
          { simp only [true_and, finset.mem_univ, finset.mem_filter, fin.coe_mk], exact hb, },
          { simp only [ι, fin.cast_succ_mk, fin.eta], }, },
    /- now we can concentrate on the last calculation -/
    rw [← eq, ← finset.sum_add_distrib],
    apply finset.sum_eq_zero,
    intros i hi,
    simp only [term1, term2],
    repeat { rw assoc, },
    simp only [true_and, finset.mem_univ, finset.mem_filter] at hi,
    have hia : i≤ fin.cast_succ (⟨a, by linarith⟩ : fin(n+1)),
    { simp only [fin.cast_succ_mk],
      rw fin.le_iff_coe_le_coe,
      simp only [fin.coe_mk],
      linarith, },
    have δσ_rel := δ_comp_σ_of_le X hia,
    simp only [fin.succ_mk] at δσ_rel,
    rw δσ_rel,
    apply add_eq_zero_iff_eq_neg.mpr,
    rw ← neg_smul,
    congr',
    simp only [fin.coe_cast_succ],
    ring_exp, },
end

lemma Hσφ_eq_zero {Y : C} {n q : ℕ} (hqn : n<q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  by_cases hqnp : n+1<q;
  simp only [Hσ, homotopy.null_homotopic_map_f (cs_down_succ (n+1)) (cs_down_succ n),
    hσ'_eq_zero hqn (cs_down_succ n)],
  { simp only [hσ'_eq_zero hqnp (cs_down_succ (n+1)), add_zero, zero_comp, comp_zero], },
  { have eqq := le_antisymm (not_lt.mp hqnp) (nat.succ_le_iff.mpr hqn),
    simp only [hσ'_eq (show n+1=0+q, by linarith) (cs_down_succ (n+1)), eq_to_hom_refl,
      pow_zero, one_zsmul, comp_id, comp_zero, zero_add],
    erw chain_complex.of_d,
    simp only [alternating_face_map_complex.obj_d, comp_sum],
    rw remove_trailing_zeros_in_sum (show n+3=2+(n+1), by linarith),
    { rw [leave_out_last_term (show 1<n+3, by linarith),
        leave_out_last_term (show 0<n+3, by linarith)],
      rw [finset.sum_eq_zero], swap,
      { intros x hx,
        exfalso,
        simpa only [finset.not_mem_empty, nat.not_lt_zero, finset.filter_false] using hx, },
      simp only [fin.mk_zero, comp_neg, fin.coe_zero, comp_add, fin.coe_one,
        pow_one, one_zsmul, zero_add, neg_smul, fin.mk_one, pow_zero],
      apply add_neg_eq_zero.mpr,
      erw [δ_comp_σ_self, δ_comp_σ_succ], },
    { intro j,
      simp only [comp_zsmul, fin.mk_zero],
      have δσ_rel := δ_comp_σ_of_gt X (_ : fin.cast_succ (0 : fin(n+1))<j.succ),
      swap, rw fin.cast_succ_zero, exact fin.succ_pos j,
      simp only [fin.cast_succ_zero] at δσ_rel,
      have h1 : j.succ.succ = translate_fin 2 _ j,
      { simp only [translate_fin],
        ext,
        simp only [fin.coe_succ, fin.coe_mk],
        linarith, },
      swap, { rw [show 2+(n+1)=n+3, by linarith], },
      rw h1 at δσ_rel,
      rw δσ_rel,
      have dφ := v.vanishing j _, swap, rw eqq, exact le_add_self,
      simp only [← assoc, dφ, zero_comp, smul_zero'], }, },
end

lemma higher_faces_vanish_ind {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]} 
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ + Hσ q).f (n+1)) :=
{ vanishing :=
  begin
    intros j hj,
    simp only [add_comp, comp_add, homological_complex.add_f_apply, homological_complex.id_f],
    erw comp_id,
    -- when n < q, the result follows immediately from the assumption
    by_cases hqn : n<q,
    { rw [Hσφ_eq_zero hqn v, zero_comp, add_zero, v.vanishing j (by linarith)], },
    -- we now assume that n≥q, and write n=a+q
    rw [not_lt] at hqn,
    cases nat.le.dest hqn with a ha,
    rw [Hσφ_eq_neg_σδ (show n=a+q, by linarith) v,
      neg_comp, add_neg_eq_zero, assoc, assoc],
    cases n with m hm,
    -- the boundary case n=0
    { simp only [nat.eq_zero_of_add_eq_zero_left ha, fin.eq_zero j,
        fin.mk_zero, fin.mk_one],
      erw [δ_comp_σ_succ],
      simp only [fin.succ_zero_eq_one, comp_id], },
    -- in the other cases, we need to write n as m+1
    { by_cases hj1 : m.succ+1≤(j : ℕ)+q,
      { have hj0 := fin.is_lt j,
        have ham : a≤m,
        { by_contradiction,
          rw [not_le, ← nat.succ_le_iff] at h,
          linarith, },
        have haj : a<(j:ℕ) := by linarith,
        have ineq1 : (fin.cast_succ (⟨a, nat.lt_succ_iff.mpr ham⟩ : fin(m+1)) < j),
        { rw fin.lt_iff_coe_lt_coe, exact haj, },
        erw [δ_comp_σ_of_gt X ineq1],
        -- we shall deal with the case a=m, i.e q=0 separately later
        by_cases ha' : a<m,
        { have ineq2 : (fin.cast_succ (⟨a+1, nat.succ_lt_succ ha'⟩ : fin(m+1)) ≤ j),
          { simp only [fin.le_iff_coe_le_coe, fin.cast_succ_mk, fin.eta, fin.coe_mk],
            exact nat.succ_le_iff.mpr haj, },
          have δδ_rel := δ_comp_δ X ineq2,
          simp only [fin.cast_succ_mk, fin.eta] at δδ_rel,
          slice_rhs 2 3 { erw [← δδ_rel], },
          simp only [← assoc],
          repeat { rw v.vanishing j (by linarith), },
          simp only [zero_comp], },
        { -- case where a=m, q=0, j=m+1
          have eqa1 : a=m := le_antisymm ham (not_lt.mp ha'),
          have eqq  : q=1,
          { simp [← eqa1] at ha,
            rw [show a.succ=a+1, by refl] at ha,
            rw add_comm at ha,
            exact (add_right_inj a).mp ha, },
          have eqa2 : a+1 = (j : ℕ) := by linarith,
          have eqj : (⟨a+1, by linarith⟩ : fin (m+3)) = (fin.cast_succ j),
          { ext, simpa [fin.coe_cast_succ, fin.coe_mk] using eqa2, },
          rw eqj,
          slice_rhs 2 3 { rw δ_comp_δ_self, },
          repeat { rw [← assoc], },
          repeat { rw v.vanishing j (by linarith), },
          simp only [zero_comp], }, },
      { simp [show a = (j : ℕ), by linarith],
        erw [δ_comp_σ_succ],
        simp only [comp_id],
        congr,
        ext,
        simp only [fin.coe_succ, fin.coe_mk], }, },
  end }

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _[n+1] ⟶ X _[n]` when k≠0 and k≥n-q+2 -/
lemma higher_faces_vanish_P : Π (q : ℕ),
  Π (n : ℕ), higher_faces_vanish q (((P q).f (n+1) : X _[n+1] ⟶ X _[n+1]))
| 0    := λ n, { vanishing := by
  { intros j hj, exfalso, have hj2 := fin.is_lt j, linarith, } }
|(q+1) := λ n, { vanishing := by
  { unfold P,
    exact (higher_faces_vanish_ind (higher_faces_vanish_P q n)).vanishing, }, }

lemma downgrade_vanishing {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish (q+1) φ) : higher_faces_vanish q φ :=
{ vanishing :=
  begin
    intros j hj,
    apply v.vanishing j,
    rw ← add_assoc,
    exact le_add_right hj,
  end }

lemma P_is_identity_where_faces_vanish {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]} 
  (v : higher_faces_vanish q φ) : φ ≫ (P q).f (n+1) = φ :=
begin
  induction q with q hq,
  { unfold P,
    simp only [homological_complex.id_f, comp_id],
    erw [comp_id], },
  { unfold P,
    simp only [comp_add, homological_complex.comp_f,
      homological_complex.add_f_apply, comp_id, ← assoc],
    simp only [hq (downgrade_vanishing v)],
    apply add_right_eq_self.mpr,
    by_cases hqn : n<q,
    { exact Hσφ_eq_zero hqn (downgrade_vanishing v), },
    { cases nat.le.dest (not_lt.mp hqn) with a ha,
      have hnaq : n=a+q := by linarith,
      simp [Hσφ_eq_neg_σδ hnaq (downgrade_vanishing v), neg_eq_zero],
      have eq := v.vanishing ⟨a, by linarith⟩ _, swap,
      { simp only [hnaq, fin.coe_mk, (show q.succ=q+1, by refl), add_assoc], },
      simp only [fin.succ_mk] at eq,
      simp only [← assoc, eq, zero_comp], }, },
end
  
lemma P_is_a_projector (q : ℕ) : (P q : (alternating_face_map_complex C).obj X ⟶ _) ≫ P q = P q :=
begin
  ext n,
  simp only [homological_complex.comp_f],
  cases n,
  { simp only [P_deg0_eq q, comp_id], },
  { exact P_is_identity_where_faces_vanish (higher_faces_vanish_P q n), },
end

/-- inductive construction of homotopies from `P q` to `𝟙` -/
noncomputable def P_is_homotopic_to_id : Π (q : ℕ),
  homotopy (P q : (alternating_face_map_complex C).obj X ⟶ _) (𝟙 _)
| 0     := homotopy.refl _
| (q+1) :=
  begin
    have h := homotopy.add (P_is_homotopic_to_id q)
      (homotopy.comp_left (homotopy_Hσ_to_zero q X) (P q)),
    refine homotopy.trans (homotopy.of_eq _) (homotopy.trans h (homotopy.of_eq _)),
    { unfold P, simp only [comp_add, comp_id], },
    { simp only [add_zero, comp_zero], }, 
  end

lemma homotopies_P_id_are_eventually_constant {q : ℕ} {n : ℕ} (hqn : n<q):
  (((P_is_homotopic_to_id (q+1)).hom ⟨⟨n,n+1⟩,cs_down_succ n⟩) : X _[n] ⟶ X _[n+1]) =
  (P_is_homotopic_to_id q).hom ⟨⟨n,n+1⟩,cs_down_succ n⟩ := 
begin
  unfold P_is_homotopic_to_id,
  simp only [homotopy.trans, homotopy.of_eq, homotopy.comp_left, homotopy.add,
    zero_add, homotopy.comp_prehomotopy, pi.add_apply,
    add_zero, add_right_eq_self, homotopy_Hσ_to_zero, homotopy.null_homotopy],
  erw [hσ'_eq_zero hqn (cs_down_succ n), comp_zero],
end

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
def P_infty : ((alternating_face_map_complex C).obj X ⟶ 
(alternating_face_map_complex C).obj X) :=
begin
  apply chain_complex.of_hom _ _ _ _ _ _
    (λ n, ((P n).f n : X _[n] ⟶ _ )),
  intro n,
  simp only,
  rw ← P_is_eventually_constant (rfl.ge : n≤n),
  have eq : ((_ : _ ⟶ X _[n]) = _ ) :=  (P (n+1)).comm (n+1) n,
  erw chain_complex.of_d at eq,
  assumption,
end

lemma P_infty_termwise (n : ℕ) : (P_infty.f n : X _[n] ⟶  X _[n] ) = 
  (P n).f n := by refl

lemma P_infty_termwise_is_a_projector (n : ℕ) :
  (P_infty.f n : X _[n] ⟶ X _[n]) ≫ (P_infty.f n) = P_infty.f n :=
begin
  simp only [homological_complex.comp_f, P_infty_termwise],
  rw [← homological_complex.comp_f, P_is_a_projector n],
end

lemma P_infty_is_a_projector : (P_infty : (alternating_face_map_complex C).obj X ⟶ _) ≫ P_infty = P_infty :=
by { ext n, rw [homological_complex.comp_f, P_infty_termwise_is_a_projector], }

/-- Construction of the homotopy from `P_infty` to the identity using eventually 
(termwise) constant homotopies from `P q` to the identity for all q -/
def P_infty_is_homotopic_to_id :
  homotopy (P_infty : (alternating_face_map_complex C).obj X ⟶ _) (𝟙 _) :=
{ hom := λ ij, (P_is_homotopic_to_id (ij.val.1+2)).hom ij,
  comm := begin 
    ext n,
    cases n,
    { have h : ((_ : X _[0] ⟶ _) = _) := (P_is_homotopic_to_id 2).comm_ext 0,
      simp only [P_infty_termwise, homological_complex.add_f_apply,
        homological_complex.id_f] at h ⊢,
      erw homotopy.null_homotopic_map_f_of_not_rel_left
        (cs_down_succ 0) cs_down_0_not_rel_left at h ⊢,
      simpa only [P_deg0_eq] using h, },
    { have h : ((_ : X _[n+1] ⟶ _) = _) :=
        (P_is_homotopic_to_id (n+2)).comm_ext (n+1),
      simp only [P_infty_termwise, homological_complex.add_f_apply],
      erw homotopy.null_homotopic_map_f (cs_down_succ (n+1)) (cs_down_succ n) at h ⊢,
      rw homotopies_P_id_are_eventually_constant (lt_add_one (n+1)),
      rwa ← P_is_eventually_constant (rfl.ge : n+1 ≤ n+1), },
  end }

/-!
## Results when the category is abelian
-/

variables {A : Type*} [category A] [abelian A]
variable {Y : simplicial_object A}

lemma higher_faces_vanish_on_Moore_complex (n : ℕ) :
  higher_faces_vanish (n+1) ((inclusion_of_Moore_complex_map Y).f (n+1)) := 
{ vanishing := λ j hj,
  begin
    simp only [inclusion_of_Moore_complex_map, chain_complex.of_hom],
    erw ← factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ
      _ j (by simp only [finset.mem_univ])),
    slice_lhs 2 3 { rw kernel_subobject_arrow_comp, },
    rwa [comp_zero],
  end }

lemma P_infty_on_Moore_complex :
(inclusion_of_Moore_complex_map Y) ≫ P_infty = (inclusion_of_Moore_complex_map Y) :=
begin
  ext n,
  simp only [homological_complex.comp_f],
  cases n,
  { simp only [P_infty_termwise, P_deg0_eq, comp_id], },
  { simp only [P_infty_termwise],
    exact P_is_identity_where_faces_vanish (higher_faces_vanish_on_Moore_complex n), },
end

lemma P_infty_factors_thru_Moore_complex_degree_wise (n : ℕ) :
  subobject.factors (normalized_Moore_complex.obj_X Y n) (P_infty.f n) :=
begin
  simp only [P_infty_termwise],
  cases n,
  { simp only [normalized_Moore_complex.obj_X],
    apply top_factors, },
  { simp only [normalized_Moore_complex.obj_X],
    rw finset_inf_factors _,
    intros i hi,
    apply limits.kernel_subobject_factors,
    exact (higher_faces_vanish_P (n+1) n).vanishing i (le_add_self), }
end

/-- P_infty factors through the normalized_Moore_complex -/
def P_infty_into_Moore_subcomplex (Y : simplicial_object A) :
  (alternating_face_map_complex A).obj Y ⟶ (normalized_Moore_complex A).obj Y :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, factor_thru _ _ (P_infty_factors_thru_Moore_complex_degree_wise n))
  (λ n,
    begin
      apply (cancel_mono (normalized_Moore_complex.obj_X Y n).arrow).mp,
      simp only [assoc, factor_thru_arrow],
      have eq := (inclusion_of_Moore_complex_map Y).comm' (n+1) n (by simp only [complex_shape.down_rel]),
      rw [(show (inclusion_of_Moore_complex_map Y).f n = (normalized_Moore_complex.obj_X Y n).arrow, by refl),
        (show ((normalized_Moore_complex A).obj Y).d (n+1) n = normalized_Moore_complex.obj_d Y n,
          by erw chain_complex.of_d)] at eq,
      erw [← eq, ← assoc, factor_thru_arrow,
        P_infty.comm' (n+1) n (by simp only [complex_shape.down_rel]), chain_complex.of_d],   
    end)

lemma P_infty_is_a_retraction (Y : simplicial_object A) :
  inclusion_of_Moore_complex_map Y ≫ P_infty_into_Moore_subcomplex Y = 𝟙 _ :=
begin
  ext n,
  simp only [homological_complex.comp_f, inclusion_of_Moore_complex_map_f, homological_complex.id_f, id_comp,
    P_infty_into_Moore_subcomplex, chain_complex.of_hom],
  slice_lhs 2 3 { erw factor_thru_arrow,},
  simp only [P_infty_termwise],
  cases n,
  { simp only [P_deg0_eq 0, comp_id], },
  { refine P_is_identity_where_faces_vanish _,
    exact
      { vanishing := λ j hj,
        begin
          dsimp,
          rw [← factor_thru_arrow _ _ (finset_inf_arrow_factors finset.univ _ j
            (by simp only [finset.mem_univ])), assoc, kernel_subobject_arrow_comp, comp_zero],
        end }, }
end

lemma factors_P_infty (Y : simplicial_object A) :
  P_infty_into_Moore_subcomplex Y ≫ inclusion_of_Moore_complex_map Y = P_infty := by
{ ext n,
  simp only [P_infty_into_Moore_subcomplex, chain_complex.of_hom,
    factor_thru_arrow, homological_complex.comp_f, inclusion_of_Moore_complex_map_f], }

/-- the inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[ext]
def homotopy_equiv_inclusion_of_Moore_complex :
  homotopy_equiv ((normalized_Moore_complex A).obj Y)
    ((alternating_face_map_complex A).obj Y) :=
{ hom := inclusion_of_Moore_complex_map Y,
  inv := P_infty_into_Moore_subcomplex Y,
  homotopy_hom_inv_id := homotopy.of_eq (P_infty_is_a_retraction Y),
  homotopy_inv_hom_id := homotopy.trans (homotopy.of_eq (factors_P_infty Y))
      P_infty_is_homotopic_to_id, }

end dold_kan

end algebraic_topology
