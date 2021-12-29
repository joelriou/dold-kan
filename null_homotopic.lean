/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homotopy

/-!
# Null homotopic maps
-/

open category_theory
open category_theory.limits
open category_theory.category
open category_theory.preadditive

noncomputable theory
open_locale classical

namespace homological_complex

universes v u
variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]
variables {c : complex_shape ι} {C D : homological_complex V c}

@[simps]
def null_homotopic_map (hom : Π i j, C.X i ⟶ D.X j) : C ⟶ D :=
{ f      := λ i, d_next i hom + prev_d i hom,
  comm'  := λ i j hij,
  begin
    have eq1 :prev_d i hom ≫ D.d i j = 0,
    { rcases h : c.prev i with _|⟨i',w⟩,
      { dsimp [prev_d], rw h, erw zero_comp, },
      { rw [prev_d_eq hom w, assoc, D.d_comp_d' i' i j w hij, comp_zero], }, },
    have eq2 : C.d i j ≫ d_next j hom = 0,
    { rcases h : c.next j with _|⟨j',w⟩,
      { dsimp [d_next], rw h, erw comp_zero, },
      { rw [d_next_eq hom w, ← assoc, C.d_comp_d' i j j' hij w, zero_comp], }, },
    rw [d_next_eq hom hij, prev_d_eq hom hij, comp_add, add_comp,
      eq1, eq2, add_zero, zero_add, assoc], 
  end }

@[simp]
def null_homotopic_map' (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) : C ⟶ D :=
null_homotopic_map (λ i j, dite (c.rel j i) (h i j) (λ _, 0))

@[simps]
def null_homotopy (hom : Π i j, C.X i ⟶ D.X j) (zero' : ∀ i j, ¬ c.rel j i → hom i j = 0) :
  homotopy (null_homotopic_map hom) 0 :=
{ hom := hom,
  zero' := zero',
  comm := by { intro i, rw [homological_complex.zero_f_apply, add_zero], refl, }, }

@[simps]
def null_homotopy' (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  homotopy (null_homotopic_map' h) 0 := by
{ apply null_homotopy (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  intros i j hij,
  dsimp,
  rw [dite_eq_right_iff],
  intro hij',
  exfalso,
  exact hij hij', }

@[simp]
lemma null_homotopy_f {k₂ k₁ k₀ : ι} (r₂₁ : c.rel k₂ k₁) (r₁₀ : c.rel k₁ k₀)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁ := by
{ dsimp, rw [d_next_eq hom r₁₀, prev_d_eq hom r₂₁], }

@[simp]
lemma null_homotopy_f' {k₂ k₁ k₀  : ι} (r₂₁ : c.rel k₂ k₁) (r₁₀ : c.rel k₁ k₀)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ + h k₁ k₂ r₂₁ ≫ D.d k₂ k₁ := by
{ simp only [← null_homotopic_map'],
  rw null_homotopy_f r₂₁ r₁₀ (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  dsimp,
  split_ifs,
  refl, }

@[simp]
lemma null_homotopy_f_lower_end {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀ := by
{ dsimp,
  rw prev_d_eq hom r₁₀,
  rcases h : c.next k₀ with _|⟨l,w⟩, swap, exfalso, exact hk₀ l w,
  dsimp [d_next], rw h, erw zero_add, }

@[simp]
lemma null_homotopy_f_lower_end' {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₀ = h k₀ k₁ r₁₀ ≫ D.d k₁ k₀ := by
{ simp only [← null_homotopic_map'],
  rw null_homotopy_f_lower_end r₁₀ hk₀ (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  dsimp,
  split_ifs,
  refl, }

@[simp]
lemma null_homotopy_f_higher_end {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₁ : ∀ l : ι, ¬c.rel l k₁)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ := by
{ dsimp,
  rw d_next_eq hom r₁₀,
  rcases h : c.prev k₁ with _|⟨l,w⟩, swap, exfalso, exact hk₁ l w,
  dsimp [prev_d], rw h, erw add_zero, }

@[simp]
lemma null_homotopy_f_higher_end' {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₁ : ∀ l : ι, ¬c.rel l k₁)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ := by
{ simp only [← null_homotopic_map'],
  rw null_homotopy_f_higher_end r₁₀ hk₁ (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  dsimp,
  split_ifs,
  refl, }

@[simp]
lemma null_homotopy_f_middle_of_nowhere {k₀ : ι} 
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l) (hk₀' : ∀ l : ι, ¬c.rel l k₀)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₀ = 0 := by
{ dsimp,
  rcases h1 : c.next k₀ with _|⟨l,w⟩, swap, exfalso, exact hk₀ l w,
  rcases h2 : c.prev k₀ with _|⟨l,w⟩, swap, exfalso, exact hk₀' l w,
  dsimp [d_next, prev_d],
  rw [h1, h2],
  erw zero_add,
  refl, }

@[simp]
lemma null_homotopy_f_middle_of_nowhere' {k₀ : ι} 
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l) (hk₀' : ∀ l : ι, ¬c.rel l k₀)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₀ = 0 := by
{ simp only [← null_homotopic_map'],
  exact null_homotopy_f_middle_of_nowhere hk₀ hk₀'
    (λ i j, dite (c.rel j i) (h i j) (λ _, 0)), }

end homological_complex

