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
import category_theory.limits.preserves.shapes.products
import algebraic_topology.split_simplicial_object

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite
open simplex_category
open_locale simplicial

universe u

variables {C : Type*} [category C]

namespace simplicial_object

namespace splitting
/-
/-- The index set which appears in the definition of split simplicial objects. -/
def index_set (Δ : simplex_categoryᵒᵖ) :=
Σ (Δ' : simplex_categoryᵒᵖ), { α : Δ.unop ⟶ Δ'.unop // epi α }
-/
namespace index_set
/--/
/-- The element in `splitting.index_set Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
def mk {Δ Δ' : simplex_category} (f : Δ ⟶ Δ') [epi f] : index_set (op Δ) :=
⟨op Δ', f, infer_instance⟩

variables {Δ' Δ : simplex_categoryᵒᵖ} (A : index_set Δ)

/-- The epimorphism in `simplex_category` associated to `A : splitting.index_set Δ` -/
def e := A.2.1

instance : epi A.e := A.2.2

lemma ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := by tidy

lemma ext (A₁ A₂ : index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.e ≫ eq_to_hom (by rw h₁) = A₂.e) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  simp only [eq_to_hom_refl, comp_id, index_set.e] at h₂,
  simp only [h₂],
end

instance : fintype (index_set Δ) :=
fintype.of_injective
  ((λ A, ⟨⟨A.1.unop.len, nat.lt_succ_iff.mpr
    (simplex_category.len_le_of_epi (infer_instance : epi A.e))⟩, A.e.to_order_hom⟩) :
    index_set Δ → (sigma (λ (k : fin (Δ.unop.len+1)), (fin (Δ.unop.len+1) → fin (k+1)))))
begin
  rintros ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h₁,
  induction Δ₁ using opposite.rec,
  induction Δ₂ using opposite.rec,
  simp only at h₁,
  have h₂ : Δ₁ = Δ₂ := by { ext1, simpa only [subtype.mk_eq_mk] using h₁.1, },
  subst h₂,
  refine ext _ _ rfl _,
  ext : 2,
  exact eq_of_heq h₁.2,
end
variable (Δ)

/-- The distinguished element in `splitting.index_set Δ` which corresponds to the
identity of `Δ`. -/
def id : index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

instance : inhabited (index_set Δ) := ⟨id Δ⟩
-/

variables {Δ : simplex_categoryᵒᵖ} (A : index_set Δ)

/-- The condition that an element `splitting.index_set Δ` is the distinguished
element `splitting.index_set.id Δ`. -/
@[simp]
def eq_id : Prop := A = id _

lemma eq_id_iff_eq : A.eq_id ↔ A.1 = Δ :=
begin
  split,
  { intro h,
    dsimp at h,
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

lemma eq_id_iff_len_eq : A.eq_id ↔ A.1.unop.len = Δ.unop.len :=
begin
  rw eq_id_iff_eq,
  split,
  { intro h,
    rw h, },
  { intro h,
    rw ← unop_inj_iff,
    ext,
    exact h, },
end

lemma eq_id_iff_len_le : A.eq_id ↔ Δ.unop.len ≤ A.1.unop.len :=
begin
  split,
  { intro h,
    rw eq_id_iff_len_eq at h,
    rw h, },
  { intro h,
    rw eq_id_iff_len_eq,
    refine le_antisymm (len_le_of_epi (infer_instance : epi A.e)) h, },
end

lemma eq_id_iff_mono : A.eq_id ↔ mono A.e :=
begin
  split,
  { intro h,
    dsimp at h,
    subst h,
    dsimp only [id, e],
    apply_instance, },
  { intro h,
    rw eq_id_iff_len_le,
    exact len_le_of_mono h, }
end

@[simps]
def epi_comp {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (A : index_set Δ₁) (p : Δ₁ ⟶ Δ₂) [epi p.unop] :
  index_set Δ₂ := ⟨A.1, ⟨p.unop ≫ A.e, epi_comp _ _⟩⟩

end index_set

variables (N : ℕ → C) (Δ : simplex_categoryᵒᵖ)
  (X : simplicial_object C) (φ : Π n, N n ⟶ X _[n])

open simplex_category
/-
/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : splitting.index_set Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
direct sum of objects in such a family. -/
@[simp, nolint unused_arguments]
def summand (A : index_set Δ) : C := N A.1.unop.len

variable [has_finite_coproducts C]

/-- The direct sum of the family `summand N Δ` -/
@[simp]
def sum := sigma_obj (summand N Δ)

variable {Δ}

/-- The inclusion of a summand in the direct sum. -/
@[simp]
def ι_sum (A : index_set Δ) : N A.1.unop.len ⟶ sum N Δ := sigma.ι _ A

variables {N}

/-- The canonical morphism `sum N Δ ⟶ X.obj Δ` attached to a sequence
of objects `N` and a sequence of morphisms `N n ⟶ X _[n]`. -/
@[simp]
def map (Δ : simplex_categoryᵒᵖ) : sum N Δ ⟶ X.obj Δ :=
sigma.desc (λ A, φ A.1.unop.len ≫ X.map A.e.op)
-/
end splitting

variable [has_finite_coproducts C]
/-
/-- A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _[n]` such that
for all `Δ : simplex_categoryhᵒᵖ`, the canonical map `splitting.map X ι Δ`
is an isomorphism. -/
@[nolint has_nonempty_instance]
structure splitting (X : simplicial_object C) :=
(N : ℕ → C) (ι : Π n, N n ⟶ X _[n])
(map_is_iso' : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (splitting.map X ι Δ))

namespace splitting

variables {X Y : simplicial_object C} (s : splitting X)

instance map_is_iso (Δ : simplex_categoryᵒᵖ) : is_iso (splitting.map X s.ι Δ) :=
s.map_is_iso' Δ

/-- The isomorphism on simplices given by the axiom `splitting.map_is_iso'` -/
@[simps]
def iso (Δ : simplex_categoryᵒᵖ) : sum s.N Δ ≅ X.obj Δ :=
as_iso (splitting.map X s.ι Δ)

/-- Via the isomorphism `s.iso Δ`, this is the inclusion of a summand
in the direct sum decomposition given by the splitting `s : splitting X`. -/
def ι_summand {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.N A.1.unop.len ⟶ X.obj Δ :=
splitting.ι_sum s.N A ≫ (s.iso Δ).hom

@[reassoc]
lemma ι_summand_eq {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A = s.ι A.1.unop.len ≫ X.map A.e.op :=
begin
  dsimp only [ι_summand, iso.hom],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

lemma ι_summand_id (n : ℕ) : s.ι_summand (index_set.id (op [n])) = s.ι n :=
by { erw [ι_summand_eq, X.map_id, comp_id], refl, }

/-- As it is stated in `splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _[n]` to the distinguished summands in each degree `n`. -/
@[simp]
def φ (f : X ⟶ Y) (n : ℕ) : s.N n ⟶ Y _[n] := s.ι n ≫ f.app (op [n])

@[simp, reassoc]
lemma ι_summand_comp_app (f : X ⟶ Y) {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op :=
by simp only [ι_summand_eq_assoc, φ, nat_trans.naturality, assoc]

lemma hom_ext' {Z : C} {Δ : simplex_categoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
  (h : ∀ (A : index_set Δ), s.ι_summand A ≫ f = s.ι_summand A ≫ g) :
    f = g :=
begin
  rw ← cancel_epi (s.iso Δ).hom,
  ext A,
  discrete_cases,
  simpa only [ι_summand_eq, iso_hom, colimit.ι_desc_assoc, cofan.mk_ι_app, assoc] using h A,
end

lemma hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g :=
begin
  ext Δ,
  apply s.hom_ext',
  intro A,
  induction Δ using opposite.rec,
  induction Δ using simplex_category.rec with n,
  dsimp,
  simp only [s.ι_summand_comp_app, h],
end

/-- The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : splitting X`  -/
def desc {Z : C} (Δ : simplex_categoryᵒᵖ)
  (F : Π (A : index_set Δ), s.N A.1.unop.len ⟶ Z) : X.obj Δ ⟶ Z :=
(s.iso Δ).inv ≫ sigma.desc F

@[simp, reassoc]
lemma ι_desc {Z : C} (Δ : simplex_categoryᵒᵖ)
  (F : Π (A : index_set Δ), s.N A.1.unop.len ⟶ Z) (A : index_set Δ) :
  s.ι_summand A ≫ s.desc Δ F = F A :=
begin
  dsimp only [ι_summand, desc],
  simp only [assoc, iso.hom_inv_id_assoc, ι_sum],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end-/

namespace splitting

variables {X Y : simplicial_object C} (s : splitting X)

@[reassoc]
lemma ι_summand_epi_naturality {Δ₁ Δ₂ : simplex_categoryᵒᵖ} (A : index_set Δ₁)
  (p : Δ₁ ⟶ Δ₂) [epi p.unop] :
  s.ι_summand A ≫ X.map p = s.ι_summand (A.epi_comp p) :=
begin
  dsimp [ι_summand],
  erw [colimit.ι_desc, colimit.ι_desc, cofan.mk_ι_app, cofan.mk_ι_app],
  dsimp only [index_set.epi_comp, index_set.e],
  rw [op_comp, X.map_comp, assoc, quiver.hom.op_unop],
end

def whiskering {D : Type*} [category D] [has_finite_coproducts D]
  {X : simplicial_object C} (s : splitting X)
  (F : C ⥤ D) [hF : ∀ (J : Type) [fintype J], preserves_colimits_of_shape (discrete J) F] :
  splitting (((simplicial_object.whiskering _ _).obj F).obj X) :=
{ N := λ n, F.obj (s.N n),
  ι := λ n, F.map (s.ι n),
  map_is_iso' := λ Δ, begin
    let X' := ((simplicial_object.whiskering C D).obj F).obj X,
    let N' := λ n, F.obj (s.N n),
    let ι' : Π (n : ℕ), N' n ⟶ X'.obj (op [n]) := λ n, F.map (s.ι n),
    let α := F.map (splitting.map X s.ι Δ),
    let e := preserves_coproduct.iso F (splitting.summand s.N Δ),
    change is_iso (map X' ι' Δ),
    rw [show map X' ι' Δ = e.inv ≫ α, by tidy],
    apply_instance,
  end, }

def of_iso {X X' : simplicial_object C} (s : splitting X) (e : X ≅ X') :
  splitting X' :=
{ N := s.N,
  ι := λ n, s.ι n ≫ e.hom.app (op [n]),
  map_is_iso' := λ Δ, begin
    let ι' : Π (n : ℕ), s.N n ⟶ X'.obj (op [n]) := λ n, s.ι n ≫ e.hom.app (op [n]),
    change is_iso (splitting.map X' ι' Δ),
    rw [show splitting.map X' ι' Δ = (s.iso Δ).hom ≫ e.hom.app Δ, by tidy],
    apply_instance,
  end, }

end splitting

end simplicial_object

namespace sSet

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

lemma simplex_category.hom.fintype (Δ₁ Δ₂ : simplex_category) : fintype (Δ₁ ⟶ Δ₂) :=
begin
  refine fintype.of_injective (λ f, f.to_order_hom.to_fun) _,
  intros f₁ f₂ eq,
  ext : 2,
  exact eq,
end

instance (n : ℕ) : degreewise_finite Δ[n] := ⟨λ Δ, simplex_category.hom.fintype _ _⟩

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
