/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.limits.shapes.finite_products

noncomputable theory

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

namespace mono_inclusion_sub_coproduct

variables {I J : Type*} [fintype I] [decidable_eq I] [fintype J] [mono_in C] (X : I → C) (γ : J → I)
  (hγ : function.injective γ)

def α : sigma_obj (λ j, X (γ j)) ⟶ sigma_obj X := sigma.desc (λ j, sigma.ι _ (γ j))
def β : sigma_obj (λ (k : (finset.image γ ⊤)ᶜ), X k) ⟶ sigma_obj X := sigma.desc (λ k, sigma.ι _ k)
def φ := coprod.desc (α X γ) (β X γ)
def index (i : I) (hi : i ∈ finset.image γ ⊤) : J := (finset.mem_image.mp hi).some
lemma index_cond (i : I) (hi : i ∈ finset.image γ ⊤) : i = γ (index γ i hi) :=
(finset.mem_image.mp hi).some_spec.some_spec.symm

include hγ

lemma index_eq (i : I) (j : J) (hj : i = γ j) : index γ i (by { simp only [finset.mem_image],
  exact ⟨j, finset.mem_univ j, hj.symm⟩, }) = j :=
begin
  apply hγ,
  rw [← index_cond γ i, hj],
end

omit hγ

def ψ₁ (i : I) (hi : i ∈ finset.image γ ⊤) : X i ⟶ sigma_obj (λ j, X (γ j)) :=
eq_to_hom (by { congr, exact index_cond γ i hi,}) ≫ sigma.ι _ (index γ i hi)

lemma sigma.congr_ι {J D : Type*} [category D] (F : J → D) [has_coproduct F]
  (a b : J) (h : a = b) : eq_to_hom (by rw h) ≫ sigma.ι F a = sigma.ι F b :=
by { subst h, simp only [eq_to_hom_refl, id_comp], }

include hγ

lemma ψ₁_eq_ι (j : J) : ψ₁ X γ (γ j) (by { rw finset.mem_image, exact ⟨j, finset.mem_univ _, rfl⟩}) =
  sigma.ι _ j :=
sigma.congr_ι (λ (j : J), X (γ j)) (index γ (γ j) _) j (index_eq γ hγ (γ j) j rfl)

omit hγ

def ψ₂ (i : I) (hi : ¬ i ∈ (finset.image γ ⊤)) :
  X i ⟶ sigma_obj (λ (k : (finset.image γ ⊤)ᶜ), X k) :=
sigma.ι (λ (k : (finset.image γ ⊤)ᶜ), X k) ⟨i, by simpa only [finset.mem_compl] using hi⟩

lemma ψ₂_eq_ι (i : I) (hi : ¬ i ∈ (finset.image γ ⊤)) :
  ψ₂ X γ i hi = sigma.ι (λ (k : (finset.image γ ⊤)ᶜ), X k)
    ⟨i, by simpa only [finset.mem_compl] using hi⟩ := sorry

def ψ : sigma_obj X ⟶ sigma_obj (λ j, X (γ j)) ⨿ sigma_obj (λ (k : (finset.image γ ⊤)ᶜ), X k) :=
sigma.desc (λ i, begin
  by_cases hi : i ∈ finset.image γ finset.univ,
  { exact ψ₁ X γ i hi ≫ coprod.inl, },
  { exact ψ₂ X γ i hi ≫ coprod.inr, },
end)

include hγ
def iso : sigma_obj (λ j, X (γ j)) ⨿ sigma_obj (λ (k : (finset.image γ ⊤)ᶜ), X k) ≅ sigma_obj X :=
{ hom := φ X γ,
  inv := ψ X γ,
  hom_inv_id' := begin
    dsimp only [φ, ψ, α, β],
    ext; discrete_cases,
    { rw [coprod.inl_desc_assoc, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc,
        cofan.mk_ι_app, comp_id],
      dsimp,
      rw dif_pos, swap,
      { simp only [finset.mem_image],
        exact ⟨j, finset.mem_univ _, rfl⟩, },
      erw ψ₁_eq_ι X γ hγ j, },
    { rw [coprod.inr_desc_assoc, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc,
        cofan.mk_ι_app, comp_id],
      dsimp,
      rw dif_neg, swap,
      { simpa only [finset.mem_compl] using j.2, },
      rw ψ₂_eq_ι X γ j,
      congr,
      simp only [finset.mk_coe], },
  end,
  inv_hom_id' := sorry, }

end mono_inclusion_sub_coproduct

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
--    have h : i ∈ finset.image γ ⊤ := sorry,
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
