/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.additive.basic
import for_mathlib.idempotents.functor_extension
import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import for_mathlib.simplex_category.simplex_category2
import for_mathlib.dold_kan.notations

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
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

/-- The index set which appears in the definition of the functor
`Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`. -/
def Γ_index_set (Δ : simplex_category) := Σ (Δ' : simplex_category), { α : Δ ⟶ Δ' // epi α }

namespace Γ_index_set

variables {Δ' Δ : simplex_category} (A : Γ_index_set Δ)

/-- The epimorphism in `simplex_category` associated to `A : Γ_index_set Δ` -/
def e := A.2.1

instance : epi A.e := A.2.2

lemma ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := by tidy

lemma ext (A₁ A₂ : Γ_index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.e ≫ eq_to_hom h₁ = A₂.e) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  simp only [eq_to_hom_refl, comp_id, Γ_index_set.e] at h₂,
  congr',
end

instance : fintype (Γ_index_set Δ) :=
  fintype.of_injective ((λ A, ⟨⟨A.1.len,
  nat.lt_succ_iff.mpr (simplex_category.len_le_of_epi (infer_instance : epi A.e))⟩, A.e.to_order_hom⟩) :
Γ_index_set Δ → (sigma (λ (k : fin (Δ.len+1)), (fin (Δ.len+1) → fin (k+1)))))
begin
  rintros ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h,
  simp only at h,
  have h₃ : Δ₁ = Δ₂ := by { ext1, simpa only [subtype.mk_eq_mk] using h.1, },
  subst h₃,
  refine ext _ _ rfl _,
  ext1, ext1,
  exact eq_of_heq h.2,
end

variable (Δ)

/-- The distinguished element in `Γ_index_set Δ` which corresponds to the
identity of `Δ`. -/
def id : Γ_index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

instance : inhabited (Γ_index_set Δ) := ⟨id Δ⟩

variables {Δ}

lemma eq_id_iff : A = id _ ↔ A.1 = Δ :=
begin
  split,
  { intro h,
    rw h,
    refl, },
  { intro h,
    rcases A with ⟨Δ', ⟨f, hf⟩⟩,
    simp only at h,
    subst h,
    refine ext _ _ rfl _,
    { haveI := hf,
      simp only [eq_to_hom_refl, comp_id],
      exact simplex_category.eq_id_of_epi f, }, },
end

lemma eq_id_iff' : A = id _ ↔ A.1.len = Δ.len :=
begin
  rw eq_id_iff,
  split,
  { intro h,
    rw h, },
  { intro h,
    ext,
    exact h, },
end

variable (θ : Δ' ⟶ Δ)

/-- When `A : Γ_index_set Δ` and `θ : Δ' → Δ` is a morphism in `simplex_category`,
the simplicial morphism `(Γ₀.obj _).map θ` sends the term of the direct sum corresponding
to `A` to the term corresponding to `A.pull θ`. It is given by the epimorphism `e`, which
appears in the epi-mono factorisation `θ ≫ A.e = e ≫ m`. -/
def pull : Γ_index_set Δ' := ⟨_, ⟨factor_thru_image (θ ≫ A.e), infer_instance⟩⟩

lemma fac_pull : (A.pull θ).e ≫ image.ι (θ ≫ A.snd.val) = θ ≫ A.e :=
image.fac (θ ≫ A.e)

end Γ_index_set

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
def summand (A : Γ_index_set Δ) : C := K.X A.1.len

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : Γ_index_set Δ` -/
def obj₂ : C := ∐ (λ (A : Γ_index_set Δ), summand K Δ A)

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
lemma map_on_summand (A : Γ_index_set Δ) {θ : Δ' ⟶ Δ}
  {e : Δ' ⟶ Δ''} {i : Δ'' ⟶ A.1} [epi e] [mono i]
  (fac : e ≫ i = θ ≫ A.e) : (sigma.ι (summand K Δ) A) ≫ map K θ =
  termwise.map_mono K i ≫ sigma.ι (summand K Δ') ⟨Δ'', ⟨e, by apply_instance⟩⟩ :=
begin
  simp only [map, colimit.ι_desc, cofan.mk_ι_app, Γ_index_set.pull],
  have h := simplex_category.image_eq fac,
  unfreezingI { subst h, },
  congr,
  { exact simplex_category.image_ι_eq fac, },
  { dsimp only [Γ_index_set.pull],
    congr,
    exact simplex_category.factor_thru_image_eq fac, },
end

@[reassoc]
lemma map_on_summand' (A : Γ_index_set Δ) (θ : Δ' ⟶ Δ) :
  (sigma.ι (summand K Δ) A) ≫ map K θ =
  termwise.map_mono K (image.ι (θ ≫ A.e)) ≫ sigma.ι (summand K _) (A.pull θ) :=
map_on_summand K A (A.fac_pull θ)

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
    erw [obj.map_on_summand K A fac, obj.termwise.map_mono_id, id_comp, comp_id],
    unfreezingI { rcases A with ⟨Δ', ⟨e, he⟩⟩, },
    congr,
  end,
  map_comp' := λ Δ'' Δ' Δ θ' θ, begin
    ext A,
    cases A,
    have fac : θ.unop ≫ θ'.unop ≫ A.e = (θ' ≫ θ).unop ≫ A.e := by rw [unop_comp, assoc],
    rw [← image.fac (θ'.unop ≫ A.e), ← assoc,
      ← image.fac (θ.unop ≫ factor_thru_image (θ'.unop ≫ A.e)), assoc] at fac,
    simpa only [obj.map_on_summand'_assoc K A θ'.unop, obj.map_on_summand' K _ θ.unop,
      obj.termwise.map_mono_comp_assoc, obj.map_on_summand K A fac],
  end }

/-- The functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`, on objects. -/
@[simps]
def map {K K' : chain_complex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' :=
{ app := λ Δ, limits.sigma.map (λ (A : Γ_index_set Δ.unop), f.f A.1.len),
  naturality' := λ Δ' Δ θ, begin
    ext A,
    simpa only [obj_map, obj.map, ι_colim_map_assoc,
      discrete.nat_trans_app, cofan.mk_ι_app, image.as_ι, colimit.ι_desc_assoc,
      ι_colim_map, colimit.ι_desc, assoc] using obj.termwise.map_mono_naturality_assoc _ _ _,
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
    ext Δ A,
    simp only [Γ₀.map_app, discrete.nat_trans_app, ι_colim_map, nat_trans.id_app,
      homological_complex.id_f],
    erw [id_comp, comp_id],
  end,
  map_comp' := λ K K' K'' f f', begin
    ext Δ A,
    simp only [Γ₀.map_app, homological_complex.comp_f, discrete.nat_trans_app,
      ι_colim_map, ι_colim_map_assoc, assoc, nat_trans.comp_app],
  end, }

/-- The inclusion of a summand of `K[Γ₀.obj K].X n` -/
abbreviation ι_Γ₀_summand {n : ℕ}
  (A : Γ_index_set [n]) : Γ₀.obj.summand K [n] A ⟶ K[Γ₀.obj K].X n  :=
sigma.ι (Γ₀.obj.summand K [n]) A

lemma eq_ι_Γ₀_summand {n : ℕ} (A : Γ_index_set [n]) :
  sigma.ι (Γ₀.obj.summand K A.1) (Γ_index_set.id A.1) ≫
    (Γ₀.obj K).map A.e.op = ι_Γ₀_summand K A :=
begin
  rw [Γ₀.obj_map, quiver.hom.unop_op,
    Γ₀.obj.map_on_summand K (Γ_index_set.id A.1)
    (show A.e ≫ 𝟙 _ = A.e ≫ 𝟙 _, by refl),
    Γ₀.obj.termwise.map_mono_id, A.ext'],
  apply id_comp,
end

/-- The extension of `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
on the idempotent completions. It shall be an equivalence of categories
for any additive category `C`. -/
@[simps]
def Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) :=
(category_theory.idempotents.functor_extension'' _ _).obj Γ₀

end dold_kan

end algebraic_topology
