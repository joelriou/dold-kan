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
import for_mathlib.split_simplicial_object

/-!

# Construction of the inverse functor of the Dold-Kan equivalence

In this file, we construct the functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories. We also extend this functor `Γ₀` as a functor
`Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` on the idempotent
completion, and this functor shall be an equivalence of categories when `C` is any additive
category (see `equivalence_additive.lean`).

When `K` is a chain_complex, `Γ₀.obj K` is a simplicial object which sends `op Δ` to
the direct sum of copies of `K.X m` for any tuple `(Δ', α)` where `α : Δ → Δ'`
is an epimorphism in `simplex_category`. The index set of this direct sum is denoted
`Γ_index_set Δ`.

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open opposite
open simplex_category
open_locale simplicial dold_kan

namespace simplex_category

namespace splitting_index_set

variables {Δ' Δ : simplex_category} (A : splitting_index_set Δ) (θ : Δ' ⟶ Δ)

instance : strong_epi (factor_thru_image θ) :=
strong_epi_factor_thru_image_of_strong_epi_mono_factorisation
  (has_strong_epi_mono_factorisations.has_fac θ).some

instance : epi (factor_thru_image θ) := strong_epi.epi

/-- When `A : Γ_index_set Δ` and `θ : Δ' → Δ` is a morphism in `simplex_category`,
the simplicial morphism `(Γ₀.obj _).map θ` sends the term of the direct sum corresponding
to `A` to the term corresponding to `A.pull θ`. It is given by the epimorphism `e`, which
appears in the epi-mono factorisation `θ ≫ A.e = e ≫ m`. -/
def pull : splitting_index_set Δ' := ⟨_, ⟨factor_thru_image (θ ≫ A.e), infer_instance⟩⟩

lemma fac_pull : (A.pull θ).e ≫ image.ι (θ ≫ A.snd.val) = θ ≫ A.e :=
image.fac (θ ≫ A.e)

end splitting_index_set

end simplex_category

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]
variables (K K' : chain_complex C ℕ) (f : K ⟶ K')
variables {Δ'' Δ' Δ : simplex_category}

/-- `is_d₀ i` is a simple condition used to check whether a monomorphism in
`simplex_category` is the coface maps `δ 0`. -/
@[nolint unused_arguments]
def is_d₀ (i : Δ' ⟶ Δ) [mono i] : Prop := (Δ.len = Δ'.len+1) ∧ (i.to_order_hom 0 ≠ 0)

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

variables (Δ' Δ)

namespace obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : Γ_index_set Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (A : splitting_index_set Δ) : C := K.X A.1.len

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : Γ_index_set Δ` -/
def obj₂ : C := ∐ (λ (A : splitting_index_set Δ), summand K Δ A)

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

variables {Δ'' Δ' Δ}
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
def map (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (θ : Δ' ⟶ Δ) :
  obj₂ K Δ ⟶ obj₂ K Δ' :=
sigma.desc (λ A, termwise.map_mono K (image.ι (θ ≫ A.e)) ≫
  (sigma.ι (summand K Δ') (A.pull θ)))

variables {Δ Δ'}

@[reassoc]
lemma map_on_summand₀ (A : splitting_index_set Δ) {θ : Δ' ⟶ Δ}
  {e : Δ' ⟶ Δ''} {i : Δ'' ⟶ A.1} [epi e] [mono i]
  (fac : e ≫ i = θ ≫ A.e) : (sigma.ι (summand K Δ) A) ≫ map K θ =
  termwise.map_mono K i ≫ sigma.ι (summand K Δ') ⟨Δ'', ⟨e, by apply_instance⟩⟩ :=
begin
  simp only [map, colimit.ι_desc, cofan.mk_ι_app, simplex_category.splitting_index_set.pull],
  have h := simplex_category.image_eq fac,
  unfreezingI { subst h, },
  congr,
  { exact simplex_category.image_ι_eq fac, },
  { dsimp only [simplex_category.splitting_index_set.pull],
    congr,
    exact simplex_category.factor_thru_image_eq fac, },
end

@[reassoc]
lemma map_on_summand₁ (A : splitting_index_set Δ) (θ : Δ' ⟶ Δ) :
  (sigma.ι (summand K Δ) A) ≫ map K θ =
  termwise.map_mono K (image.ι (θ ≫ A.e)) ≫ sigma.ι (summand K _) (A.pull θ) :=
map_on_summand₀ K A (A.fac_pull θ)

end obj

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on objects. -/
@[simps]
def obj (K : chain_complex C ℕ) : simplicial_object C :=
{ obj := λ Δ, obj.obj₂ K (unop Δ),
  map := λ Δ Δ' θ, obj.map K θ.unop,
  map_id' := λ Δ, begin
    ext A,
    cases A,
    have fac : A.e ≫ 𝟙 A.1 = 𝟙 Δ.unop ≫ A.e := by rw [comp_id, id_comp],
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
    simpa only [obj.map_on_summand₁_assoc K A θ'.unop, obj.map_on_summand₁ K _ θ.unop,
      obj.termwise.map_mono_comp_assoc, obj.map_on_summand₀ K A fac],
  end }

lemma splitting_map_eq_id (Δ : simplex_categoryᵒᵖ) :
  (simplicial_object.splitting.map (Γ₀.obj K) (λ (n : ℕ), sigma.ι (Γ₀.obj.summand K [n]) (splitting_index_set.id [n])) Δ)
    = 𝟙 _ :=
begin
  ext A,
  discrete_cases,
  induction Δ using opposite.rec,
  induction Δ with n,
  dsimp,
  simp only [colimit.ι_desc, cofan.mk_ι_app, comp_id, Γ₀.obj_map],
  rw [Γ₀.obj.map_on_summand₀ K
    (simplex_category.splitting_index_set.id A.1) (show A.e ≫ 𝟙 _ = A.e ≫ 𝟙 _, by refl),
    Γ₀.obj.termwise.map_mono_id, A.ext'],
  apply id_comp,
end

def splitting (K : chain_complex C ℕ) :
  simplicial_object.splitting (Γ₀.obj K) :=
{ N := λ n, K.X n,
  ι := λ n, sigma.ι (Γ₀.obj.summand K [n]) (splitting_index_set.id [n]),
  is_iso' := λ Δ, begin
    rw Γ₀.splitting_map_eq_id,
    apply is_iso.id,
  end, }

@[simp]
lemma splitting_iso_hom_eq_id (Δ : simplex_category): ((splitting K).iso Δ).hom = 𝟙 _ :=
splitting_map_eq_id K (op Δ)

variables {Δ Δ'}

@[reassoc]
lemma obj.map_on_summand (A : splitting_index_set Δ) (θ : Δ' ⟶ Δ)
  {e : Δ' ⟶ Δ''} {i : Δ'' ⟶ A.1} [epi e] [mono i]
  (fac : e ≫ i = θ ≫ A.e) : (Γ₀.splitting K).ι_summand A ≫ (Γ₀.obj K).map θ.op =
  Γ₀.obj.termwise.map_mono K i ≫ (Γ₀.splitting K).ι_summand ⟨Δ'', e, infer_instance⟩ :=
begin
  dsimp only [simplicial_object.splitting.ι_summand,
    simplicial_object.splitting.ι_sum],
  simp only [assoc, Γ₀.splitting_iso_hom_eq_id, id_comp, comp_id],
  exact Γ₀.obj.map_on_summand₀ K A fac,
end

@[reassoc]
lemma obj.map_on_summand' (A : splitting_index_set Δ) (θ : Δ' ⟶ Δ) :
  (splitting K).ι_summand A ≫ (obj K).map θ.op =
    obj.termwise.map_mono K (image.ι (θ ≫ A.e)) ≫ (splitting K).ι_summand (A.pull θ) :=
by { apply obj.map_on_summand, apply image.fac, }

@[reassoc]
lemma obj.map_mono_on_summand_id (i : Δ' ⟶ Δ) [mono i] :
  (splitting K).ι_summand (splitting_index_set.id Δ) ≫ (obj K).map i.op =
  obj.termwise.map_mono K i ≫ (splitting K).ι_summand (splitting_index_set.id Δ') :=
obj.map_on_summand K (splitting_index_set.id Δ) i (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by refl)

@[reassoc]
lemma obj.map_epi_on_summand_id (e : Δ' ⟶ Δ) [epi e] :
  (Γ₀.splitting K).ι_summand (splitting_index_set.id Δ) ≫ (Γ₀.obj K).map e.op =
    (Γ₀.splitting K).ι_summand ⟨Δ, ⟨e, infer_instance⟩⟩ :=
by simpa only [Γ₀.obj.map_on_summand K (splitting_index_set.id Δ) e
    (rfl : e ≫ 𝟙 Δ = e ≫ 𝟙 Δ), Γ₀.obj.termwise.map_mono_id] using id_comp _

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on morphisms. -/
@[simps]
def map {K K' : chain_complex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' :=
{ app := λ Δ, (Γ₀.splitting K).desc Δ (λ A, f.f A.1.len ≫ (Γ₀.splitting K').ι_summand A),
  naturality' := λ Δ' Δ θ, begin
    apply (Γ₀.splitting K).hom_ext',
    intro A,
    erw [(splitting K).ι_desc_assoc, obj.map_on_summand'_assoc K _ θ.unop,
      (splitting K).ι_desc, assoc, obj.map_on_summand' K' _ θ.unop,
      obj.termwise.map_mono_naturality_assoc],
  end, }

end Γ₀

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, which is
the inverse functor of the Dold-Kan equivalence in the category abelian
categories, or more generally pseudoabelian categories. -/
@[simps]
def Γ₀ : chain_complex C ℕ ⥤ simplicial_object C :=
{ obj := Γ₀.obj,
  map := λ _ _, Γ₀.map,
  map_id' := λ K, begin
    apply (Γ₀.splitting K).hom_ext,
    intro n,
    simpa only [simplicial_object.splitting.φ, ← simplicial_object.splitting.ι_summand_id,
      Γ₀.map_app, homological_complex.id_f, nat_trans.id_app, comp_id,
      (Γ₀.splitting K).ι_desc (op [n])] using id_comp _,
  end,
  map_comp' := λ K K' K'' f f', begin
    apply (Γ₀.splitting K).hom_ext,
    intro n,
    simp only [simplicial_object.splitting.φ, ← simplicial_object.splitting.ι_summand_id,
      Γ₀.map_app, nat_trans.comp_app, assoc, homological_complex.comp_f,
      (Γ₀.splitting K).ι_desc (op [n]), (Γ₀.splitting K).ι_desc_assoc (op [n]),
      (Γ₀.splitting K').ι_desc (op [n])],
  end, }

/-- The extension of `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`. -/
@[simps]
def Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) :=
(category_theory.idempotents.functor_extension₂ _ _).obj Γ₀

end dold_kan

end algebraic_topology
