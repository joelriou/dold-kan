/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.zero_morphisms
import category_theory.limits.types
import category_theory.concrete_category
import category_theory.morphism_property
import category_theory.limits.mono_coprod

universes v u

noncomputable theory

open category_theory category_theory.category category_theory.limits

namespace category_theory

namespace limits

variables {C : Type*} [category C] [has_finite_coproducts C]

section

lemma congr_colimit_ι {J D : Type*} [category J] [category D] (F : J ⥤ D) [has_colimit F]
  {j₁ j₂ : J} (h : j₁ = j₂) :
  colimit.ι F j₁ = eq_to_hom (by rw h) ≫ colimit.ι F j₂ :=
by { subst h, rw [eq_to_hom_refl, id_comp], }

lemma congr_sigma_ι {J D : Type*} [category D] (X : J → D) [has_coproduct X]
  {j₁ j₂ : J} (h : j₁ = j₂) :
  sigma.ι X j₁ = eq_to_hom (by rw h) ≫ sigma.ι X j₂ :=
congr_colimit_ι (discrete.functor X) (congr_arg discrete.mk h)

@[simp]
def coproduct_pullback {A B : Type*} (X : B → C) (f : A → B) [has_coproduct X]
  [has_coproduct (X ∘ f)] : ∐ (X ∘ f) ⟶ ∐ X := sigma.desc (λ a, sigma.ι _ (f a))

@[simps]
def coproduct_pullback_iso {A B : Type*} (X : B → C) (e : A ≃ B) [has_coproduct X]
  [has_coproduct (X ∘ e)] : ∐ (X ∘ e) ≅ ∐ X :=
{ hom := coproduct_pullback X e,
  inv := sigma.desc (λ b, eq_to_hom (by simp) ≫ sigma.ι _ (e.symm b)),
  hom_inv_id' := begin
    ext a,
    discrete_cases,
    simp only [coproduct_pullback, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc, comp_id],
    exact (congr_sigma_ι (X ∘ e) (e.symm_apply_apply a).symm).symm,
  end,
  inv_hom_id' := begin
    ext b,
    discrete_cases,
    simp only [coproduct_pullback, colimit.ι_desc_assoc, cofan.mk_ι_app, assoc, colimit.ι_desc,
      comp_id],
    exact (congr_sigma_ι X (e.apply_symm_apply b).symm).symm,
  end, }

instance mono_coproduct_pullback_inl [mono_coprod C] {A B : Type*} (X : A ⊕ B → C)
  [has_coproduct X] [has_coproduct (X ∘ sum.inl)] [has_coproduct (X ∘ sum.inr)] :
  mono (coproduct_pullback X sum.inl) :=
begin
  let c : binary_cofan (∐ (X ∘ sum.inl)) ((∐ (X ∘ sum.inr))) := binary_cofan.mk
    (coproduct_pullback X sum.inl) (coproduct_pullback X sum.inr),
  have hc : is_colimit c := begin
    refine binary_cofan.is_colimit.mk c _ _ _ _,
    { intros T f₁ f₂,
      refine sigma.desc (λ x, _),
      cases x,
      { refine _ ≫ f₁, exact sigma.ι (X ∘ sum.inl) x, },
      { refine _ ≫ f₂, exact sigma.ι (X ∘ sum.inr) x, }, },
    { intros T f₁ f₂, ext, discrete_cases, simp, },
    { intros T f₁ f₂, ext, discrete_cases, simp, },
    { intros T f₁ f₂ m hm₁ hm₂,
      ext x,
      discrete_cases,
      tidy, },
  end,
  exact mono_coprod.binary_cofan_inl c hc,
end

lemma mono_coproduct_pullback_of_injective [mono_coprod C] [has_finite_coproducts C]
  {A B : Type*} [fintype A] [fintype B] (X : B → C) (f : A → B) (hf : function.injective f) :
  mono (coproduct_pullback X f) :=
begin
  let A' := (set.image f set.univ)ᶜ,
  let g : A ⊕ A' → B := λ x, by { cases x, exacts [f x, x.1], },
  have hg : function.bijective g,
  { split,
    { rintros (a₁|a₁') (a₂|a₂'),
      { tidy, },
      { intro h,
        exfalso,
        exact a₂'.2 ⟨a₁, ⟨set.mem_univ _, h⟩⟩, },
      { intro h,
        exfalso,
        exact a₁'.2 ⟨a₂, ⟨set.mem_univ _, h.symm⟩⟩, },
      { tidy, }, },
    { intro b,
      by_cases ∃ (a : A), b = f a,
      { cases h with a ha,
        exact ⟨sum.inl a, ha.symm⟩, },
      { exact ⟨sum.inr ⟨b, λ h', h ⟨h'.some, h'.some_spec.2.symm⟩⟩, rfl⟩, }, }, },
  let γ := equiv.of_bijective g hg,
  haveI : fintype A' := fintype.of_injective (λ a', a'.1) (λ a₁' a₂' h, by { ext, exact h, }),
  let E : arrow.mk (coproduct_pullback (X ∘ γ) sum.inl) ≅ arrow.mk (coproduct_pullback X f),
  { refine arrow.iso_mk (iso.refl _) (coproduct_pullback_iso X γ) _,
    ext a,
    discrete_cases,
    dsimp,
    simp only [id_comp, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc],
    erw [colimit.ι_desc, cofan.mk_ι_app], },
  exact ((morphism_property.respects_iso.monomorphisms C).arrow_mk_iso_iff E).mp
    (morphism_property.monomorphisms.infer_property _),
end

end

end limits

end category_theory
