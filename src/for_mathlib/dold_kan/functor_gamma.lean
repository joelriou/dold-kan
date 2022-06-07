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

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
open opposite
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]

def Γ_index_set (Δ : simplex_category) := Σ (Δ' : simplex_category), { α : Δ ⟶ Δ' // epi α }

namespace Γ_index_set

variables {Δ' Δ : simplex_category}

lemma ext (A₁ A₂ : Γ_index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.2.1 ≫ eq_to_hom h₁ = A₂.2.1) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  congr,
  simpa only [eq_to_hom_refl, comp_id] using h₂,
end

instance : fintype (Γ_index_set Δ) :=
fintype.of_injective ((λ A, ⟨⟨A.1.len,
  nat.lt_succ_iff.mpr (simplex_category.len_le_of_epi A.2.2)⟩, A.2.1.to_order_hom⟩) :
  Γ_index_set Δ → (sigma (λ (k : fin (Δ.len+1)), (fin (Δ.len+1) → fin (k+1)))))
begin
  rintros ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h,
  simp only at h,
  rcases h with ⟨h₁, h₂⟩,
  have h₃ : Δ₁ = Δ₂ := by { ext1, simpa only [subtype.mk_eq_mk] using h₁, },
  subst h₃,
  refine ext _ _ rfl _,
  ext1, ext1,
  exact eq_of_heq h₂,
end

variable (Δ)

@[simps]
def id (Δ : simplex_category) : Γ_index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

instance (Δ : simplex_category) : inhabited (Γ_index_set Δ) := ⟨id Δ⟩

variable {Δ}

lemma eq_id_iff (A : Γ_index_set Δ) :
  A = id _ ↔ A.1 = Δ :=
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

lemma eq_id_iff' (A : Γ_index_set Δ) :
  A = id _ ↔ A.1.len = Δ.len :=
begin
  rw eq_id_iff,
  split,
  { intro h,
    rw h, },
  { intro h,
    ext,
    exact h, },
end

def pull (A : Γ_index_set Δ) (θ : Δ' ⟶ Δ) :
  Γ_index_set Δ' :=
⟨_, ⟨factor_thru_image (θ ≫ A.2.1), infer_instance⟩⟩

lemma fac_pull (A : Γ_index_set Δ) (θ : Δ' ⟶ Δ) :
  (A.pull θ).2.1 ≫ image.ι (θ ≫ A.snd.val) = θ ≫ A.snd.val := image.fac (θ ≫ A.2.1)

end Γ_index_set

def Γ_summand (K : chain_complex C ℕ) (Δ : simplex_category)
  (A : Γ_index_set Δ) : C := K.X A.1.len

def Γ_termwise (K : chain_complex C ℕ) (Δ : simplex_category) : C :=
  ∐ (λ (A : Γ_index_set Δ), Γ_summand K Δ A)

@[nolint unused_arguments]
def is_d₀ {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] : Prop :=
  (Δ.len = Δ'.len+1) ∧ (i.to_order_hom 0 ≠ 0)

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

def Γ_on_mono (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] :
  K.X Δ.len ⟶ K.X Δ'.len :=
begin
  by_cases Δ = Δ',
  { apply eq_to_hom,
    congr,
    assumption, },
  { by_cases is_d₀ i,
    { exact K.d Δ.len Δ'.len, },
    { exact 0, }, },
end

namespace Γ_on_mono

variables (K K' : chain_complex C ℕ) (f : K ⟶ K') {Δ'' Δ' Δ : simplex_category}
variables (i' : Δ'' ⟶ Δ') [mono i'] (i : Δ' ⟶ Δ) [mono i]

variable (Δ)
lemma on_id : Γ_on_mono K (𝟙 Δ) = 𝟙 _ := by { unfold Γ_on_mono, tidy, }

variable {Δ}

lemma on_eq_to_hom (hi : Δ = Δ') : Γ_on_mono K i = eq_to_hom (by rw hi) :=
by { unfold Γ_on_mono, split_ifs, refl, }

lemma on_d₀ (hi : is_d₀ i) : Γ_on_mono K i = K.d Δ.len Δ'.len :=
begin
  unfold Γ_on_mono,
  split_ifs,
  { exfalso,
    cases hi with h1 h2,
    rw h at h1,
    linarith, },
  refl,
end

lemma eq_zero (h1 : ¬Δ = Δ') (h2 : ¬is_d₀ i) : Γ_on_mono K i = 0 :=
by { unfold Γ_on_mono, split_ifs, refl, }

variables {K K'}

@[simp, reassoc]
lemma naturality : Γ_on_mono K i ≫ f.f Δ'.len = f.f Δ.len ≫ Γ_on_mono K' i :=
begin
  unfold Γ_on_mono,
  split_ifs,
  { unfreezingI { subst h, },
    simp only [id_comp, eq_to_hom_refl, comp_id], },
  { rw [homological_complex.hom.comm], },
  { rw [zero_comp, comp_zero], }
end

lemma simplex_category_non_epi_mono {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] (hi : ¬Δ=Δ'):
  ∃ (k : ℕ), Δ.len = Δ'.len + (k + 1) :=
begin
  cases le_iff_exists_add.mp (simplex_category.len_le_of_mono (show mono i, by apply_instance)) with k h,
  cases k,
  { exfalso,
    rw [add_zero] at h,
    exact hi (simplex_category.ext Δ Δ' h), },
  { use k,
    exact h, },
end

variable (K)

@[simp, reassoc]
lemma comp : Γ_on_mono K i ≫ Γ_on_mono K i' = Γ_on_mono K (i' ≫ i) :=
begin
  /- case where i : Δ' ⟶ Δ is the identity -/
  by_cases h1 : Δ = Δ',
  { unfreezingI { subst h1, },
    simp only [simplex_category.eq_id_of_mono i,
      comp_id, id_comp, on_id K, eq_to_hom_refl], },
  /- case where i' : Δ'' ⟶ Δ' is the identity -/
  by_cases h2 : Δ' = Δ'',
  { unfreezingI { subst h2, },
    simp only [simplex_category.eq_id_of_mono i',
      comp_id, id_comp, on_id K, eq_to_hom_refl], },
  /- then the RHS is always zero -/
  cases simplex_category_non_epi_mono i h1 with k hk,
  cases simplex_category_non_epi_mono i' h2 with k' hk',
  have eq : Δ.len = Δ''.len + (k+k'+2) := by { rw hk' at hk, linarith, },
  rw eq_zero K (i' ≫ i) _ _, rotate,
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
    { rw [on_d₀ K i h3, on_d₀ K i' h4,
        homological_complex.d_comp_d], },
    { simp only [eq_zero K i' h2 h4, comp_zero], }, },
  { simp only [eq_zero K i h1 h3, zero_comp], },
end

end Γ_on_mono

def Γ_simplicial (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (θ : Δ' ⟶ Δ) :
  Γ_termwise K Δ ⟶ Γ_termwise K Δ' :=
sigma.desc (λ A, Γ_on_mono K (image.ι (θ ≫ A.2.1)) ≫ (sigma.ι (Γ_summand K Δ') (A.pull θ)))

@[reassoc]
lemma Γ_simplicial_on_summand (K : chain_complex C ℕ) {Δ'' Δ' Δ : simplex_category}
  (A : Γ_index_set Δ) {θ : Δ' ⟶ Δ} {e : Δ' ⟶ Δ''} {i : Δ'' ⟶ A.1} [epi e] [mono i]
  (fac : e ≫ i = θ ≫ A.2.1) :
  (sigma.ι (Γ_summand K Δ) A) ≫ Γ_simplicial K θ =
  Γ_on_mono K i ≫ sigma.ι (Γ_summand K Δ') ⟨Δ'', ⟨e, by apply_instance⟩⟩ :=
begin
  simp only [Γ_simplicial, colimit.ι_desc, cofan.mk_ι_app, Γ_index_set.pull],
  have h := simplex_category.image_eq fac,
  unfreezingI { subst h, },
  congr,
  { exact simplex_category.image_ι_eq fac, },
  { dsimp only [Γ_index_set.pull],
    congr,
    exact simplex_category.factor_thru_image_eq fac, },
end

@[reassoc]
lemma Γ_simplicial_on_summand' (K : chain_complex C ℕ) {Δ' Δ : simplex_category}
  (A : Γ_index_set Δ) (θ : Δ' ⟶ Δ) :
  (sigma.ι (Γ_summand K Δ) A) ≫ Γ_simplicial K θ =
  Γ_on_mono K (image.ι (θ ≫ A.2.1)) ≫ sigma.ι (Γ_summand K _) (A.pull θ) :=
Γ_simplicial_on_summand K A (A.fac_pull θ)

namespace Γ₀_functor

@[simps]
def obj (K : chain_complex C ℕ) : simplicial_object C :=
{ obj := λ Δ, Γ_termwise K (unop Δ),
  map := λ Δ Δ' θ, Γ_simplicial K θ.unop,
  map_id' := λ Δ, begin
    ext A,
    cases A,
    haveI : epi A.2.1 := A.2.2,
    have fac : A.2.1 ≫ 𝟙 A.1 = 𝟙 Δ.unop ≫ A.2.1 := by rw [comp_id, id_comp],
    erw [Γ_simplicial_on_summand K A fac, Γ_on_mono.on_id, id_comp, comp_id],
    unfreezingI { rcases A with ⟨Δ', ⟨e, he⟩⟩, },
    congr,
  end,
  map_comp' := λ Δ'' Δ' Δ θ' θ, begin
    ext A,
    cases A,
    have fac : θ.unop ≫ θ'.unop ≫ A.2.1 = (θ' ≫ θ).unop ≫ A.2.1 := by rw [unop_comp, assoc],
    rw [← image.fac (θ'.unop ≫ A.2.1), ← assoc,
      ← image.fac (θ.unop ≫ factor_thru_image (θ'.unop ≫ A.snd.val)), assoc] at fac,
    simpa only [Γ_simplicial_on_summand'_assoc K A θ'.unop, Γ_simplicial_on_summand' K _ θ.unop,
      Γ_on_mono.comp_assoc, Γ_simplicial_on_summand K A fac],
  end }

@[simps]
def map {K K' : chain_complex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' :=
{ app := λ Δ, limits.sigma.map (λ (A : Γ_index_set Δ.unop), f.f A.1.len),
  naturality' := λ Δ' Δ θ, begin
    ext A,
    simpa only [obj_map, Γ_simplicial, ι_colim_map_assoc,
      discrete.nat_trans_app, cofan.mk_ι_app, image.as_ι, colimit.ι_desc_assoc,
      ι_colim_map, colimit.ι_desc, assoc] using Γ_on_mono.naturality_assoc _ _ _,
  end, }

end Γ₀_functor

@[simps]
def Γ₀ : chain_complex C ℕ ⥤ simplicial_object C :=
{ obj := Γ₀_functor.obj,
  map := λ _ _, Γ₀_functor.map,
  map_id' := λ K, begin
    ext Δ A,
    simp only [Γ₀_functor.map_app, discrete.nat_trans_app, ι_colim_map, nat_trans.id_app,
      homological_complex.id_f],
    erw [id_comp, comp_id],
  end,
  map_comp' := λ K K' K'' f f', begin
    ext Δ A,
    simp only [Γ₀_functor.map_app, homological_complex.comp_f, discrete.nat_trans_app,
      ι_colim_map, ι_colim_map_assoc, assoc, nat_trans.comp_app],
  end, }

abbreviation inclusion_Γ_summand (K : chain_complex C ℕ) {Δ : simplex_category}
  (A : Γ_index_set Δ) : Γ_summand K Δ A ⟶ K[Γ₀.obj K].X Δ.len :=
sigma.ι (Γ_summand K Δ) A

@[simps]
def Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) :=
(category_theory.idempotents.functor_extension'' _ _).obj Γ₀

end dold_kan

end algebraic_topology
