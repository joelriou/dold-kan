/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.images
import for_mathlib.simplex_category.factorisations
import category_theory.limits.shapes.finite_products
import algebraic_topology.simplicial_set

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite
open_locale simplicial

universe u

namespace simplex_category

/-- The index set which appears in the definition of split simplicial objects. -/
def splitting_index_set (Δ : simplex_category) :=
Σ (Δ' : simplex_category), { α : Δ ⟶ Δ' // epi α }

namespace splitting_index_set

variables {Δ' Δ : simplex_category} (A : splitting_index_set Δ)

/-- The epimorphism in `simplex_category` associated to `A : splitting_index_set Δ` -/
def e := A.2.1

instance : epi A.e := A.2.2

lemma ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := by tidy

lemma ext (A₁ A₂ : splitting_index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.e ≫ eq_to_hom h₁ = A₂.e) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  simp only [eq_to_hom_refl, comp_id, splitting_index_set.e] at h₂,
  congr',
end

instance : fintype (splitting_index_set Δ) :=
  fintype.of_injective ((λ A, ⟨⟨A.1.len,
  nat.lt_succ_iff.mpr (simplex_category.len_le_of_epi (infer_instance : epi A.e))⟩, A.e.to_order_hom⟩) :
splitting_index_set Δ → (sigma (λ (k : fin (Δ.len+1)), (fin (Δ.len+1) → fin (k+1)))))
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
def id : splitting_index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

instance : inhabited (splitting_index_set Δ) := ⟨id Δ⟩

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

end splitting_index_set

end simplex_category

namespace simplicial_object

variables {C : Type*} [category C]

namespace splitting

variables (N : ℕ → C) (Δ : simplex_category)
  (X : simplicial_object C) (φ : Π n, N n ⟶ X _[n])

open simplex_category

@[simp]
def summand (A : splitting_index_set Δ) : C := N A.1.len

variable [has_finite_coproducts C]

@[simp]
def sum := sigma_obj (summand N Δ)

variable {Δ}

@[simp]
def ι_sum (A : splitting_index_set Δ) : N A.1.len ⟶ sum N Δ := sigma.ι _ A

variables {N X}

@[simp]
def map (Δ' : simplex_categoryᵒᵖ) : sum N Δ'.unop ⟶ X.obj Δ' :=
sigma.desc (λ A, φ A.1.len ≫ X.map A.e.op)

end splitting

variable [has_finite_coproducts C]

structure splitting (X : simplicial_object C) :=
(N : ℕ → C) (ι : Π n, N n ⟶ X _[n])-- (mono_ι : ∀ n, mono (ι n))
(is_iso' : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (splitting.map ι Δ))

namespace splitting

open simplex_category

variables {X Y : simplicial_object C} (s : splitting X) (f g : X ⟶ Y)

instance map_is_iso (Δ : simplex_categoryᵒᵖ) : is_iso (splitting.map s.ι Δ) := s.is_iso' Δ

@[simps]
def iso (Δ : simplex_categoryᵒᵖ) : sum s.N Δ.unop ≅ X.obj Δ :=
as_iso (splitting.map s.ι Δ)

@[reassoc]
lemma ι_comp_iso_hom {Δ : simplex_categoryᵒᵖ} (A : splitting_index_set Δ.unop) :
  sigma.ι _ A ≫ (s.iso Δ).hom = s.ι A.1.len ≫ X.map A.e.op :=
by simp only [iso_hom, colimit.ι_desc, cofan.mk_ι_app]

@[simp]
def φ (n : ℕ) : s.N n ⟶ Y _[n] := s.ι n ≫ f.app (op [n])

@[reassoc]
lemma ι_comp_iso_hom_comp {Δ : simplex_categoryᵒᵖ} (A : splitting_index_set Δ.unop) :
  sigma.ι _ A ≫ (s.iso Δ).hom ≫ f.app Δ = s.φ f A.1.len ≫ Y.map A.e.op :=
by simp only [ι_comp_iso_hom_assoc, φ, assoc, nat_trans.naturality]

lemma hom_ext (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g :=
begin
  ext Δ,
  rw ← cancel_epi (s.iso Δ).hom,
  ext A,
  discrete_cases,
  simp only [ι_comp_iso_hom_comp, h],
end

end splitting

end simplicial_object

namespace sSet

variables {C : Type*} [category C]

class degreewise_finite (X : sSet.{u}) := (finite' : ∀ (Δ : simplex_categoryᵒᵖ), fintype (X.obj Δ))

restate_axiom degreewise_finite.finite'
attribute [instance] degreewise_finite.finite

@[simps]
def tensor (X : sSet.{u}) (Y : C)
  [∀ (Δ : simplex_categoryᵒᵖ), has_coproduct (λ (x : X.obj Δ), Y)] : simplicial_object C :=
{ obj := λ Δ, sigma_obj (λ (x : X.obj Δ), Y),
  map := λ Δ₁ Δ₂ θ, sigma.desc (λ x, sigma.ι (λ (y : X.obj Δ₂), Y) (X.map θ x)),
  map_id' := λ Δ, begin
    ext,
    discrete_cases,
    erw [colimit.ι_desc, cofan.mk_ι_app, comp_id, X.map_id],
    refl,
  end,
  map_comp' := λ Δ₁ Δ₂ Δ₃ θ θ', begin
    ext,
    discrete_cases,
    simp only [colimit.ι_desc, cofan.mk_ι_app, colimit.ι_desc_assoc],
    congr,
    rw [X.map_comp],
    refl,
  end, }

def tensor_ι {X : sSet.{u}} {Δ : simplex_categoryᵒᵖ} (x : X.obj Δ) (Y : C)
  [∀ (Δ : simplex_categoryᵒᵖ), has_coproduct (λ (x : X.obj Δ), Y)] :
  Y ⟶ (X.tensor Y).obj Δ :=
sigma.ι _ x

@[simp, reassoc]
lemma tensor_ι_comp_map {X : sSet.{u}} {Δ Δ' : simplex_categoryᵒᵖ} (x : X.obj Δ) (Y : C)
  [∀ (Δ : simplex_categoryᵒᵖ), has_coproduct (λ (x : X.obj Δ), Y)]
  (θ : Δ ⟶ Δ') :
  tensor_ι x Y ≫ (X.tensor Y).map θ = tensor_ι (X.map θ x) Y :=
begin
  dsimp [tensor_ι],
  simp only [colimit.ι_desc, cofan.mk_ι_app],
end

instance (n : ℕ) : degreewise_finite Δ[n] :=
⟨begin
  sorry,
end⟩

instance has_coproduct_of_degreewise_finite
  (X : sSet.{u}) [degreewise_finite X] (Δ : simplex_categoryᵒᵖ) [has_finite_coproducts C]
  (Y : C) : has_coproduct (λ (x : X.obj Δ), Y) := infer_instance

def tensor_yoneda_adjunction [has_finite_coproducts C]
  (n : ℕ) (Y : C) (X : simplicial_object C) :
  (Δ[n].tensor Y ⟶ X) ≃ (Y ⟶ X.obj (op [n])) :=
{ to_fun := λ f, tensor_ι (by exact 𝟙 [n]) Y ≫ f.app (op [n]),
  inv_fun := λ g,
  { app := λ Δ, sigma.desc (λ s, g ≫ X.map (quiver.hom.op s)),
    naturality' := λ Δ₁ Δ₂ θ, begin
      ext s,
      discrete_cases,
      simpa only [tensor_map, colimit.ι_desc_assoc, cofan.mk_ι_app, colimit.ι_desc, assoc,
        ← X.map_comp],
  end, },
  left_inv := λ g, begin
    ext Δ s,
    discrete_cases,
    simp only [cofan.mk_ι_app, colimit.ι_desc, assoc,
      ← g.naturality, tensor_ι_comp_map_assoc],
    dsimp only [standard_simplex],
    simpa only [simplex_category.hom.comp, simplex_category.hom.id,
      simplex_category.small_category_id, yoneda_obj_map,
      quiver.hom.unop_op, simplex_category.small_category_comp,
      simplex_category.hom.to_order_hom_mk, order_hom.id_comp,
      simplex_category.hom.mk_to_order_hom],
  end,
  right_inv := λ f, begin
    dsimp only [tensor_ι],
    simp only [colimit.ι_desc, cofan.mk_ι_app],
    erw [op_id, X.map_id, comp_id],
  end, }

end sSet

namespace simplicial_object

namespace splitting

variables {C : Type*} [category C] [has_finite_coproducts C]
  {X : simplicial_object C} (s : splitting X)

structure candidate_sk (n : ℕ) := (Y : simplicial_object C) (i : s.N n ⟶ Y.obj (op [n]))

def sk : Π (n : ℕ), candidate_sk s n
| 0 :=
  { Y := Δ[0].tensor (s.N 0),
    i := (sSet.tensor_yoneda_adjunction 0 (s.N 0) _).to_fun (𝟙 _), }
| (n+1) := sorry

end splitting

end simplicial_object
