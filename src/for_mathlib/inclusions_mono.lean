/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.finite_products

open category_theory category_theory.category category_theory.limits

namespace category_theory


namespace limits

variables (C : Type*) [category C] [has_finite_coproducts C]
class mono_in : Prop :=
(mono_inl' : Π (A B : C) [h : has_binary_coproduct A B], mono (@coprod.inl _ _ A B h))

variable {C}

namespace mono_in

instance [hC : mono_in C] {A B : C} : mono (coprod.inl : A ⟶ A ⨿ B) := by apply hC.mono_inl'

instance [hC : mono_in C] {A B : C} : mono (coprod.inr : B ⟶ A ⨿ B) :=
begin
  have eq : (coprod.inr : B ⟶ A ⨿ B) = coprod.inl ≫ (coprod.braiding B A).hom := by simp,
  rw eq,
  apply mono_comp,
end

lemma mono_inclusion_sub_coproduct {I J : Type*} [fintype I] [fintype J] [mono_in C]
  (X : I → C) (γ : J → I) (hγ : function.injective γ) :
    mono (sigma.desc (λ j, sigma.ι _ (γ j)) : sigma_obj (λ j, X (γ j)) ⟶ sigma_obj X) :=
begin
  classical,
  let A := sigma_obj (λ j, X (γ j)),
  let K := (finset.image γ ⊤)ᶜ,
  let B := sigma_obj (λ (k : K), X k),
  let α : A ⟶ sigma_obj X := sigma.desc (λ j, sigma.ι _ (γ j)),
  let β : B ⟶ sigma_obj X := sigma.desc (λ k, sigma.ι _ k),
  let φ : A ⨿ B ⟶ sigma_obj X := coprod.desc α β,
  let ψ : sigma_obj X ⟶ A ⨿ B := sigma.desc (λ i, begin
    by_cases ∃ (j : J), i = γ j,
    { exact eq_to_hom (by { congr', exact h.some_spec, }) ≫ sigma.ι _ h.some ≫ coprod.inl, },
    { refine eq_to_hom _ ≫ sigma.ι _ (⟨i, _⟩ : K) ≫ coprod.inr,
      { simp only [finset.mem_compl, finset.mem_image, exists_prop, not_exists, not_and],
        exact λ j hj hji, h ⟨j, hji.symm⟩, },
      { refl, }, },
  end),
  haveI : is_iso φ := begin
    refine ⟨⟨ψ, ⟨_, _⟩⟩⟩,
    sorry,
    sorry,
  end,
  have eq : α = coprod.inl ≫ φ := by tidy,
  change mono α,
  rw eq,
  apply mono_comp,
end

end mono_in

end limits

end category_theory
