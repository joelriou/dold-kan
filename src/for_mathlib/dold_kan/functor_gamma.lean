/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.additive.basic
import for_mathlib.idempotents.functor_extension2
import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import for_mathlib.simplex_category.factorisations
import category_theory.limits.shapes.images
import for_mathlib.dold_kan.notations
import algebraic_topology.split_simplicial_object
import for_mathlib.dold_kan.split

/-!

# Construction of the inverse functor of the Dold-Kan equivalence

In this file, we construct the functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories. We also extend this functor `Γ₀` as a functor
`Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` on the idempotent
completion, and this functor shall be an equivalence of categories when `C` is any additive
category (see `equivalence_additive.lean`).

By definition, when `K` is a chain_complex, `Γ₀.obj K` is a simplicial object which
sends `Δ : simplex_categoryᵒᵖ` to a certain coproduct indexed by the set
`splitting.index_set Δ` whose elements consists of epimorphisms `e : Δ.unop ⟶ Δ'.unop`
(with `Δ' : simplex_categoryᵒᵖ`); the summand attached to such an `e` is `K.X Δ'.unop.len`.
By construction, `Γ₀.obj K` is a split simplicial object whose splitting is `Γ₀.splitting K`.

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open opposite
open simplex_category
open simplicial_object
open_locale simplicial dold_kan

namespace simplicial_object

namespace splitting

namespace index_set

variables {Δ' Δ : simplex_categoryᵒᵖ} (A : index_set Δ) (θ : Δ ⟶ Δ')

instance {Δ₁ Δ₂ : simplex_category} (θ : Δ₁ ⟶ Δ₂) : strong_epi (factor_thru_image θ) :=
strong_epi_factor_thru_image_of_strong_epi_mono_factorisation
  (has_strong_epi_mono_factorisations.has_fac θ).some

instance {Δ₁ Δ₂ : simplex_category} (θ : Δ₁ ⟶ Δ₂) :
  epi (factor_thru_image θ) := strong_epi.epi

/-- When `A : Γ_index_set Δ` and `θ : Δ' → Δ` is a morphism in `simplex_category`,
the simplicial morphism `(Γ₀.obj _).map θ` sends the term of the direct sum corresponding
to `A` to the term corresponding to `A.pull θ`. It is given by the epimorphism `e`, which
appears in the epi-mono factorisation `θ ≫ A.e = e ≫ m`. -/
def pull : index_set Δ' := mk (factor_thru_image (θ.unop ≫ A.e))

@[simp, reassoc]
lemma fac_pull : (A.pull θ).e ≫ image.ι (θ.unop ≫ A.e) = θ.unop ≫ A.e := image.fac _

end index_set

end splitting

end simplicial_object

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]
variables (K K' : chain_complex C ℕ) (f : K ⟶ K')

/-- `is_d₀ i` is a simple condition used to check whether a monomorphism in
`simplex_category` is the coface maps `δ 0`. -/
@[nolint unused_arguments]
def is_d₀ {Δ Δ' : simplex_category} (i : Δ' ⟶ Δ) [mono i] : Prop := (Δ.len = Δ'.len+1) ∧ (i.to_order_hom 0 ≠ 0)

namespace is_d₀

lemma iff {j : ℕ} {i : fin (j+2)} : is_d₀ (simplex_category.δ i) ↔ i = 0 :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    by_contradiction,
    exact h₂ (fin.succ_above_ne_zero_zero h), },
  { intro h,
    subst h,
    split,
    { refl, },
    { apply fin.succ_ne_zero, }, }
end

lemma eq_d₀ {n : ℕ} {i : [n] ⟶ [n+1]} [mono i] (hi : is_d₀ i) :
  i = simplex_category.δ 0 :=
begin
  cases simplex_category.eq_δ_of_mono i with j h,
  unfreezingI { subst h, },
  rw iff at hi,
  rw hi,
end

end is_d₀

namespace Γ₀

namespace obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : Γ_index_set Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (Δ : simplex_categoryᵒᵖ) (A : splitting.index_set Δ) : C := K.X A.1.unop.len

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : Γ_index_set Δ` -/
def obj₂ (Δ : simplex_categoryᵒᵖ): C := ∐ (λ (A : splitting.index_set Δ), summand K Δ A)

namespace termwise

/-- A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, and
zero otherwise. -/
def map_mono (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] :
  K.X Δ.len ⟶ K.X Δ'.len :=
begin
  by_cases Δ = Δ',
  { apply eq_to_hom,
    congr', },
  { by_cases is_d₀ i,
    { exact K.d Δ.len Δ'.len, },
    { exact 0, }, },
end

variables {Δ'' Δ' Δ : simplex_category}
variables (i' : Δ'' ⟶ Δ') [mono i'] (i : Δ' ⟶ Δ) [mono i]

variable (Δ)
lemma map_mono_id : map_mono K (𝟙 Δ) = 𝟙 _ := by { unfold map_mono, tidy, }

variable {Δ}

lemma map_mono_d₀ (hi : is_d₀ i) : map_mono K i = K.d Δ.len Δ'.len :=
begin
  unfold map_mono,
  split_ifs,
  { exfalso,
    cases hi with h1 h2,
    rw h at h1,
    linarith, },
  refl,
end

lemma map_mono_d₀' {n : ℕ} : map_mono K (δ (0 : fin (n+2))) = K.d (n+1) n :=
map_mono_d₀ K _ (by rw is_d₀.iff)

lemma map_mono_eq_zero (h₁ : ¬Δ = Δ') (h₂ : ¬is_d₀ i) : map_mono K i = 0 :=
by { unfold map_mono, split_ifs, refl, }

variables {K K'}

@[simp, reassoc]
lemma map_mono_naturality : map_mono K i ≫ f.f Δ'.len = f.f Δ.len ≫ map_mono K' i :=
begin
  unfold map_mono,
  split_ifs,
  { unfreezingI { subst h, },
    simp only [id_comp, eq_to_hom_refl, comp_id], },
  { rw homological_complex.hom.comm, },
  { rw [zero_comp, comp_zero], }
end

lemma simplex_category_non_epi_mono {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] (hi : ¬Δ=Δ'):
  ∃ (k : ℕ), Δ.len = Δ'.len + (k + 1) :=
begin
  cases le_iff_exists_add.mp (simplex_category.len_le_of_mono (infer_instance : mono i)) with k h,
  cases k,
  { exfalso,
    exact hi (simplex_category.ext Δ Δ' h), },
  { exact ⟨k, h⟩, },
end

variable (K)

@[simp, reassoc]
lemma map_mono_comp : map_mono K i ≫ map_mono K i' = map_mono K (i' ≫ i) :=
begin
  /- case where i : Δ' ⟶ Δ is the identity -/
  by_cases h1 : Δ = Δ',
  { unfreezingI { subst h1, },
    simp only [simplex_category.eq_id_of_mono i,
      comp_id, id_comp, map_mono_id K, eq_to_hom_refl], },
  /- case where i' : Δ'' ⟶ Δ' is the identity -/
  by_cases h2 : Δ' = Δ'',
  { unfreezingI { subst h2, },
    simp only [simplex_category.eq_id_of_mono i',
      comp_id, id_comp, map_mono_id K, eq_to_hom_refl], },
  /- then the RHS is always zero -/
  cases simplex_category_non_epi_mono i h1 with k hk,
  cases simplex_category_non_epi_mono i' h2 with k' hk',
  have eq : Δ.len = Δ''.len + (k+k'+2) := by { rw hk' at hk, linarith, },
  rw map_mono_eq_zero K (i' ≫ i) _ _, rotate,
  { by_contradiction,
    simpa only [self_eq_add_right,h ] using eq, },
  { by_contradiction,
    dsimp [is_d₀] at h,
    simp only [h.left, add_right_inj] at eq,
    linarith, },
  /- in all cases, the LHS is also zero,
  either by definition, or because d ≫ d = 0 -/
  by_cases h3 : is_d₀ i,
  { by_cases h4 : is_d₀ i',
    { rw [map_mono_d₀ K i h3, map_mono_d₀ K i' h4,
        homological_complex.d_comp_d], },
    { simp only [map_mono_eq_zero K i' h2 h4, comp_zero], }, },
  { simp only [map_mono_eq_zero K i h1 h3, zero_comp], },
end

end termwise

/-- The simplicial morphism on the simplicial object `Γ₀.obj K` induced by
a morphism `Δ' → Δ` in `simplex_category` is defined on each summand
associated to an `A : Γ_index_set Δ` in terms of the epi-mono factorisation
of `θ ≫ A.e`. -/
def map (K : chain_complex C ℕ) {Δ' Δ : simplex_categoryᵒᵖ} (θ : Δ ⟶ Δ') :
  obj₂ K Δ ⟶ obj₂ K Δ' :=
sigma.desc (λ A, termwise.map_mono K (image.ι (θ.unop ≫ A.e)) ≫
  (sigma.ι (summand K Δ') (A.pull θ)))

@[reassoc]
lemma map_on_summand₀ {Δ Δ' : simplex_categoryᵒᵖ} (A : splitting.index_set Δ) {θ : Δ ⟶ Δ'}
  {Δ'' : simplex_category} {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [epi e] [mono i]
  (fac : e ≫ i = θ.unop ≫ A.e) :
  (sigma.ι (summand K Δ) A) ≫ map K θ =
  termwise.map_mono K i ≫ sigma.ι (summand K Δ') (splitting.index_set.mk e) :=
begin
  simp only [map, colimit.ι_desc, cofan.mk_ι_app],
  have h := simplex_category.image_eq fac,
  unfreezingI { subst h, },
  congr,
  { exact simplex_category.image_ι_eq fac, },
  { dsimp only [simplicial_object.splitting.index_set.pull],
    congr,
    exact simplex_category.factor_thru_image_eq fac, },
end

@[reassoc]
lemma map_on_summand₁ {Δ Δ' : simplex_categoryᵒᵖ} (A : splitting.index_set Δ) (θ : Δ ⟶ Δ') :
  (sigma.ι (summand K Δ) A) ≫ map K θ =
  termwise.map_mono K (image.ι (θ.unop ≫ A.e)) ≫ sigma.ι (summand K _) (A.pull θ) :=
map_on_summand₀ K A (A.fac_pull θ)

end obj

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on objects. -/
@[simps]
def obj (K : chain_complex C ℕ) : simplicial_object C :=
{ obj := λ Δ, obj.obj₂ K Δ,
  map := λ Δ Δ' θ, obj.map K θ,
  map_id' := λ Δ, begin
    ext A,
    cases A,
    have fac : A.e ≫ 𝟙 A.1.unop = (𝟙 Δ).unop ≫ A.e := by rw [unop_id, comp_id, id_comp],
    erw [obj.map_on_summand₀ K A fac, obj.termwise.map_mono_id, id_comp, comp_id],
    unfreezingI { rcases A with ⟨Δ', ⟨e, he⟩⟩, },
    congr,
  end,
  map_comp' := λ Δ'' Δ' Δ θ' θ, begin
    ext A,
    cases A,
    have fac : θ.unop ≫ θ'.unop ≫ A.e = (θ' ≫ θ).unop ≫ A.e := by rw [unop_comp, assoc],
    rw [← image.fac (θ'.unop ≫ A.e), ← assoc,
      ← image.fac (θ.unop ≫ factor_thru_image (θ'.unop ≫ A.e)), assoc] at fac,
    simpa only [obj.map_on_summand₁_assoc K A θ', obj.map_on_summand₁ K _ θ,
      obj.termwise.map_mono_comp_assoc, obj.map_on_summand₀ K A fac],
  end }

lemma splitting_map_eq_id (Δ : simplex_categoryᵒᵖ) :
  (simplicial_object.splitting.map (Γ₀.obj K)
    (λ (n : ℕ), sigma.ι (Γ₀.obj.summand K (op [n])) (splitting.index_set.id (op [n]))) Δ)
    = 𝟙 _ :=
begin
  ext A,
  discrete_cases,
  induction Δ using opposite.rec,
  induction Δ with n,
  dsimp,
  simp only [colimit.ι_desc, cofan.mk_ι_app, comp_id, Γ₀.obj_map],
  rw [Γ₀.obj.map_on_summand₀ K
    (simplicial_object.splitting.index_set.id A.1) (show A.e ≫ 𝟙 _ = A.e.op.unop ≫ 𝟙 _, by refl),
    Γ₀.obj.termwise.map_mono_id, A.ext'],
  apply id_comp,
end

def splitting (K : chain_complex C ℕ) : simplicial_object.splitting (Γ₀.obj K) :=
{ N := λ n, K.X n,
  ι := λ n, sigma.ι (Γ₀.obj.summand K (op [n])) (splitting.index_set.id (op [n])),
  map_is_iso' := λ Δ, begin
    rw Γ₀.splitting_map_eq_id,
    apply is_iso.id,
  end, }

@[simp]
lemma splitting_iso_hom_eq_id (Δ : simplex_categoryᵒᵖ): ((splitting K).iso Δ).hom = 𝟙 _ :=
splitting_map_eq_id K Δ

@[reassoc]
lemma obj.map_on_summand {Δ Δ' : simplex_categoryᵒᵖ} (A : splitting.index_set Δ) (θ : Δ ⟶ Δ')
  {Δ'' : simplex_category}
  {e : Δ'.unop ⟶ Δ''} {i : Δ'' ⟶ A.1.unop} [epi e] [mono i]
  (fac : e ≫ i = θ.unop ≫ A.e) : (Γ₀.splitting K).ι_summand A ≫ (Γ₀.obj K).map θ =
  Γ₀.obj.termwise.map_mono K i ≫ (Γ₀.splitting K).ι_summand (splitting.index_set.mk e) :=
begin
  dsimp only [simplicial_object.splitting.ι_summand,
    simplicial_object.splitting.ι_coprod],
  simp only [assoc, Γ₀.splitting_iso_hom_eq_id, id_comp, comp_id],
  exact Γ₀.obj.map_on_summand₀ K A fac,
end

@[reassoc]
lemma obj.map_on_summand' {Δ Δ' : simplex_categoryᵒᵖ} (A : splitting.index_set Δ) (θ : Δ ⟶ Δ') :
  (splitting K).ι_summand A ≫ (obj K).map θ =
    obj.termwise.map_mono K (image.ι (θ.unop ≫ A.e)) ≫ (splitting K).ι_summand (A.pull θ) :=
by { apply obj.map_on_summand, apply image.fac, }

@[reassoc]
lemma obj.map_mono_on_summand_id {Δ Δ' : simplex_category} (i : Δ' ⟶ Δ) [mono i] :
  (splitting K).ι_summand (splitting.index_set.id (op Δ)) ≫ (obj K).map i.op =
  obj.termwise.map_mono K i ≫ (splitting K).ι_summand (splitting.index_set.id (op Δ')) :=
obj.map_on_summand K (splitting.index_set.id (op Δ)) i.op (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by refl)

@[reassoc]
lemma obj.map_epi_on_summand_id {Δ Δ' : simplex_category } (e : Δ' ⟶ Δ) [epi e] :
  (Γ₀.splitting K).ι_summand (splitting.index_set.id (op Δ)) ≫ (Γ₀.obj K).map e.op =
    (Γ₀.splitting K).ι_summand (splitting.index_set.mk e) :=
by simpa only [Γ₀.obj.map_on_summand K (splitting.index_set.id (op Δ)) e.op
    (rfl : e ≫ 𝟙 Δ = e ≫ 𝟙 Δ), Γ₀.obj.termwise.map_mono_id] using id_comp _

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on morphisms. -/
@[simps]
def map {K K' : chain_complex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' :=
{ app := λ Δ, (Γ₀.splitting K).desc Δ (λ A, f.f A.1.unop.len ≫ (Γ₀.splitting K').ι_summand A),
  naturality' := λ Δ' Δ θ, begin
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    simp only [(splitting K).ι_desc_assoc, obj.map_on_summand'_assoc K _ θ,
      (splitting K).ι_desc, assoc, obj.map_on_summand' K' _ θ],
    apply obj.termwise.map_mono_naturality_assoc,
  end, }

end Γ₀

/-- The functor `Γ₀' : chain_complex C ℕ ⥤ simplicial_object.split C`
that induces `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, which
shall be the inverse functor of the Dold-Kan equivalence for
abelian or pseudo-abelian category. -/
@[simps]
def Γ₀' : chain_complex C ℕ ⥤ simplicial_object.split C :=
{ obj := λ K, simplicial_object.split.mk' (Γ₀.splitting K),
  map := λ K K' f,
  { F := Γ₀.map f,
    f := f.f,
    comm' := λ n, by { dsimp, simpa only [← splitting.ι_summand_id,
      (Γ₀.splitting K).ι_desc], }, }, }

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, which is
the inverse functor of the Dold-Kan equivalence when `C` is an abelian
categorie, or more generally pseudoabelian categories. -/
@[simps]
def Γ₀ : chain_complex C ℕ ⥤ simplicial_object C := Γ₀' ⋙ split.forget _

/-- The extension of `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`. -/
@[simps]
def Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) :=
(category_theory.idempotents.functor_extension₂ _ _).obj Γ₀

def higher_faces_vanish.on_Γ₀_summand_id (K : chain_complex C ℕ) (n : ℕ) :
  higher_faces_vanish (n+1) ((Γ₀.splitting K).ι_summand (splitting.index_set.id (op [n+1]))) :=
begin
  intros j hj,
  have eq := Γ₀.obj.map_mono_on_summand_id K (simplex_category.δ j.succ),
  rw [Γ₀.obj.termwise.map_mono_eq_zero K, zero_comp] at eq, rotate,
  { intro h,
    exact (nat.succ_ne_self n) (congr_arg simplex_category.len h), },
  { intro h,
    simp only [is_d₀.iff] at h,
    exact fin.succ_ne_zero j h, },
  exact eq,
end

@[simp, reassoc]
lemma P_infty_on_Γ₀_splitting_summand_eq_self
  (K : chain_complex C ℕ) {n : ℕ} :
  (Γ₀.splitting K).ι_summand (splitting.index_set.id (op [n])) ≫ (P_infty : K[Γ₀.obj K] ⟶ _).f n =
    (Γ₀.splitting K).ι_summand (splitting.index_set.id (op [n])) :=
begin
  rw P_infty_f,
  cases n,
  { simpa only [P_f_0_eq] using comp_id _, },
  { exact (higher_faces_vanish.on_Γ₀_summand_id K n).comp_P_eq_self, },
end

end dold_kan

end algebraic_topology
