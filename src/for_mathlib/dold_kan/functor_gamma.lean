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

lemma ext {Δ : simplex_category} (A₁ A₂ : Γ_index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.2.1 ≫ eq_to_hom h₁ = A₂.2.1) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  congr,
  simpa only [eq_to_hom_refl, comp_id] using h₂,
end

instance {Δ : simplex_category} : fintype (Γ_index_set Δ) :=
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

@[simps]
def id (Δ : simplex_category) : Γ_index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

lemma eq_id {Δ : simplex_category} {A : Γ_index_set Δ} (h : A.1.len = Δ.len) :
  A = id Δ :=
begin
  rcases A with ⟨Δ', ⟨f, hf⟩⟩,
  have h' : Δ' = Δ := by { ext, exact h, },
  subst h',
  refine ext _ _ rfl _,
  { haveI := hf,
    simp only [eq_to_hom_refl, comp_id],
    exact simplex_category.eq_id_of_epi f, },
end

end Γ_index_set

def Γ_summand (K : chain_complex C ℕ) (Δ : simplex_category)
  (A : Γ_index_set Δ) : C := K.X A.1.len

def Γ_termwise (K : chain_complex C ℕ) (Δ : simplex_category) : C :=
  ∐ (λ (A : Γ_index_set Δ), Γ_summand K Δ A)

@[nolint unused_arguments]
def is_d₀ {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] : Prop :=
  (Δ.len = Δ'.len+1) ∧ (i.to_order_hom 0 ≠ 0)

lemma is_d₀_iff {j : ℕ} {i : fin (j+2)} : is_d₀ (simplex_category.δ i) ↔ i = 0 :=
begin
  split,
  { rintro ⟨h₁,h₂⟩,
    by_contradiction,
    erw fin.succ_above_ne_zero_zero h at h₂,
    exact h₂ rfl, },
  { intro h,
    subst h,
    split,
    { refl, },
    { erw fin.succ_above_zero,
      simp only [fin.one_eq_zero_iff, nat.succ_ne_zero, fin.succ_zero_eq_one,
        ne.def, not_false_iff], }, }
end

lemma eq_d₀_of_is_d₀ {n : ℕ} {i : [n] ⟶ [n+1]} [mono i] (hi : is_d₀ i) :
  i = simplex_category.δ 0 :=
begin
  cases simplex_category.eq_δ_of_mono i with j h,
  unfreezingI { subst h, },
  rw is_d₀_iff at hi,
  rw hi,
end

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

lemma Γ_on_mono_on_id (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i]
  (hi : Δ = Δ') : Γ_on_mono K i = eq_to_hom (by { congr, assumption, }) :=
by { unfold Γ_on_mono, split_ifs, refl, }

lemma Γ_on_mono_on_eq_to_hom (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (hi : Δ = Δ') :
  Γ_on_mono K (eq_to_hom hi.symm) = eq_to_hom (by { congr, assumption, }) :=
Γ_on_mono_on_id K (eq_to_hom hi.symm) hi

lemma Γ_on_mono_on_d0 (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i]
  (hi : is_d₀ i) : Γ_on_mono K i = K.d Δ.len Δ'.len :=
begin
  unfold Γ_on_mono,
  split_ifs,
  { exfalso,
    cases hi with h1 h2,
    rw h at h1,
    linarith, },
  refl,
end

lemma Γ_on_mono_eq_zero (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i]
  (h1 : ¬ Δ = Δ') (h2 : ¬is_d₀ i) : Γ_on_mono K i = 0 :=
by { unfold Γ_on_mono, split_ifs, refl, }

lemma Γ_on_mono_naturality {K K' : chain_complex C ℕ} (f : K ⟶ K')
  {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] :
  Γ_on_mono K i ≫ f.f Δ'.len = f.f Δ.len ≫ Γ_on_mono K' i :=
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

def Γ_on_mono_comp (K : chain_complex C ℕ) {Δ'' Δ' Δ : simplex_category}
   (i' : Δ'' ⟶ Δ') (i : Δ' ⟶ Δ) [mono i] [mono i'] :
   Γ_on_mono K i ≫ Γ_on_mono K i' = Γ_on_mono K (i' ≫ i) :=
begin
  /- case where i : Δ' ⟶ Δ is the identity -/
  by_cases h1 : Δ = Δ',
  { unfreezingI { subst h1, },
    simp only [simplex_category.eq_id_of_mono i,
      comp_id, id_comp, Γ_on_mono_on_id K, eq_to_hom_refl], },
  /- case where i' : Δ'' ⟶ Δ' is the identity -/
  by_cases h2 : Δ' = Δ'',
  { unfreezingI { subst h2, },
    simp only [simplex_category.eq_id_of_mono i',
      comp_id, id_comp, Γ_on_mono_on_id K, eq_to_hom_refl], },
  /- then the RHS is always zero -/
  cases simplex_category_non_epi_mono i h1 with k hk,
  cases simplex_category_non_epi_mono i' h2 with k' hk',
  have eq : Δ.len = Δ''.len + (k+k'+2) := by { rw hk' at hk, linarith, },
  rw Γ_on_mono_eq_zero K (i' ≫ i) _ _, rotate,
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
    { rw [Γ_on_mono_on_d0 K i h3, Γ_on_mono_on_d0 K i' h4,
        homological_complex.d_comp_d], },
    { simp only [Γ_on_mono_eq_zero K i' h2 h4, comp_zero], }, },
  { simp only [Γ_on_mono_eq_zero K i h1 h3, zero_comp], },
end

def Γ_simplicial (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (θ : Δ' ⟶ Δ) :
  Γ_termwise K Δ ⟶ Γ_termwise K Δ' :=
begin
  apply sigma.desc,
  intro A,
  let em := image.mono_factorisation (θ ≫ A.2.1),
  let A' : Γ_index_set Δ' := ⟨em.I, ⟨em.e, simplex_category.epi_of_mono_factorisation _⟩⟩,
  exact Γ_on_mono K em.m ≫ (sigma.ι (Γ_summand K Δ') A'),
end

lemma Γ_simplicial_on_summand (K : chain_complex C ℕ) {Δ'' Δ' Δ : simplex_category}
  (A : Γ_index_set Δ) {θ : Δ' ⟶ Δ} {e : Δ' ⟶ Δ''} {i : Δ'' ⟶ A.1} [epi e] [mono i]
  (h : e ≫ i = θ ≫ A.2.1) :
  (sigma.ι (Γ_summand K Δ) A) ≫ Γ_simplicial K θ =
  Γ_on_mono K i ≫ (sigma.ι (Γ_summand K Δ') ⟨Δ'', ⟨e, by apply_instance⟩⟩) :=
by { simp only [Γ_simplicial, cofan.mk_ι_app, colimit.ι_desc],
  congr'; rw simplex_category.mono_factorisation_eq e i h, }

namespace Γ₀_functor

@[simps]
def obj (K : chain_complex C ℕ) : simplicial_object C :=
{ obj := λ Δ, Γ_termwise K (unop Δ),
  map := λ Δ Δ' θ, Γ_simplicial K θ.unop,
  map_id' := λ Δ, begin
    ext A,
    cases A,
    haveI : epi A.2.1 := A.2.2,
    have eq := Γ_simplicial_on_summand K A
      (show A.2.1 ≫ 𝟙 A.1 = 𝟙 Δ.unop ≫ A.2.1, by { simp only [comp_id, id_comp], }),
    simp only [Γ_on_mono_on_id K (𝟙 A.1) (by refl), eq_to_hom_refl] at eq,
    erw [eq, id_comp, comp_id],
    congr,
    refine Γ_index_set.ext _ _ rfl _,
    simp only [eq_to_hom_refl, comp_id],
  end,
  map_comp' := λ Δ'' Δ' Δ θ' θ, begin
    ext A,
    cases A,
    let em' := image.mono_factorisation (θ'.unop ≫ A.2.1),
    haveI : epi em'.e := simplex_category.epi_of_mono_factorisation _,
    slice_rhs 1 2 { rw Γ_simplicial_on_summand K A em'.fac, },
    let em  := image.mono_factorisation (θ.unop ≫ em'.e),
    haveI : epi em.e := simplex_category.epi_of_mono_factorisation _,
    rw [assoc, Γ_simplicial_on_summand K ⟨em'.I, ⟨em'.e, by apply_instance⟩⟩ em.fac],
    have fac : em.e ≫ (em.m ≫ em'.m) = (θ' ≫ θ).unop ≫ A.2.1,
    { rw [← assoc, em.fac, assoc, em'.fac, ← assoc, unop_comp], },
    rw [Γ_simplicial_on_summand K A fac, ← assoc],
    congr',
    rw Γ_on_mono_comp,
  end }

@[simps]
def map {K K' : chain_complex C ℕ} (f : K ⟶ K') : obj K ⟶ obj K' :=
{ app := λ Δ, limits.sigma.map (λ (A : Γ_index_set Δ.unop), (f.f A.1.len)),
  naturality' := λ Δ' Δ θ, begin
    ext A,
    simp only [obj_map, Γ_simplicial, ι_colim_map_assoc,
      discrete.nat_trans_app, cofan.mk_ι_app, image.as_ι, colimit.ι_desc_assoc,
      ι_colim_map, colimit.ι_desc, assoc],
    slice_rhs 1 2 { erw ← Γ_on_mono_naturality, },
    rw [assoc],
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

@[simp]
def inclusion_Γ_summand (K : chain_complex C ℕ) {n : ℕ} (A : Γ_index_set [n]) :
  Γ_summand K [n] A ⟶ K[Γ₀.obj K].X n :=
sigma.ι (Γ_summand K [n]) A

@[simps]
def Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C) :=
(category_theory.idempotents.functor_extension'' _ _).obj Γ₀

end dold_kan

end algebraic_topology
