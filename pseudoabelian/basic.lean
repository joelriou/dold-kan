/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.preadditive.additive_functor
import category_theory.additive.basic
import category_theory.equivalence
import category_theory.functor_ext

/-!
# Pseudoabelian categories

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.preadditive
open category_theory.limits
open_locale big_operators


namespace category_theory

variables (C : Type*) [category C] [preadditive C]

namespace pseudoabelian

@[nolint has_inhabited_instance]
structure karoubi := (X : C) (p : X ⟶ X) (idempotence : p ≫ p = p)

end pseudoabelian

class is_pseudoabelian : Prop :=
(idempotents_have_kernels : Π (P : pseudoabelian.karoubi C), has_kernel P.p)

namespace pseudoabelian

namespace karoubi

variables {C}

@[ext]
lemma ext {P Q : karoubi C} (h_X : P.X = Q.X)
  (h_p : P.p ≫ eq_to_hom h_X = eq_to_hom h_X ≫ Q.p) : P = Q :=
begin
  cases P,
  cases Q,
  dsimp at h_X h_p,
  subst h_X,
  simpa only [true_and, eq_self_iff_true, id_comp, eq_to_hom_refl,
    heq_iff_eq, comp_id] using h_p,
end

@[simps]
def idempotent_of_id_sub_idempotent (P : karoubi C) : karoubi C :=
{ X := P.X,
  p := 𝟙 _ - P.p,
  idempotence := by simp only [comp_sub, sub_comp, id_comp, comp_id, P.idempotence,
    sub_self, sub_zero], }

@[ext]
structure hom (P Q : karoubi C) := (f : P.X ⟶ Q.X) (comm : f = P.p ≫ f ≫ Q.p)

instance (P Q : karoubi C) : inhabited (hom P Q) := ⟨⟨0, by rw [zero_comp, comp_zero]⟩⟩

@[ext]
lemma hom_ext {P Q : karoubi C} {f' g' : hom P Q} : f' = g' ↔ f'.f = g'.f :=
by { split; intro h, { congr, assumption, }, { ext, assumption, }, }

lemma p_comp {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.1 = f.1 :=
by rw [f.2, ← assoc, P.idempotence]

lemma comp_p {P Q : karoubi C} (f : hom P Q) : f.1 ≫ Q.p = f.1 :=
by rw [f.2, assoc, assoc, Q.idempotence]

lemma p_comm {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.1 = f.1 ≫ Q.p :=
by rw [p_comp, comp_p]

def comp_proof {P Q R : karoubi C} (g' : hom Q R) (f' : hom P Q) :
  f'.1 ≫ g'.1 = P.p ≫ (f'.1 ≫ g'.1) ≫ R.p :=
by rw [assoc, comp_p, ← assoc, p_comp]

end karoubi

instance : category (karoubi C) :=
{ hom      := karoubi.hom,
  id       := λ P, ⟨P.p, by { repeat { rw P.idempotence, }, }⟩,
  comp     := λ P Q R f' g', ⟨f'.1 ≫ g'.1, karoubi.comp_proof g' f'⟩,
  id_comp' := λ P Q f', by { ext, simp only [karoubi.p_comp], },
  comp_id' := λ P Q f', by { ext, simp only [karoubi.comp_p], },
  assoc'   := λ P Q R S f' g' h', by { ext, simp only [category.assoc], }, }

namespace karoubi

@[simp]
lemma comp {P Q R : karoubi C} (f' : P ⟶ Q) (g' : Q ⟶ R) :
  f' ≫ g' = ⟨f'.1 ≫ g'.1, comp_proof g' f'⟩ := by refl

@[simp]
lemma id_eq {P : karoubi C} : 𝟙 P = ⟨P.p, by repeat { rw P.idempotence, }⟩ := by refl

instance coe : has_coe_t C (karoubi C) := ⟨λ X, ⟨X, 𝟙 X, by rw comp_id⟩⟩

@[simp]
lemma coe_X (X : C) : (X : karoubi C).X = X := by refl

@[simp]
lemma coe_p (X : C) : (X : karoubi C).p = 𝟙 X := by refl

@[simp]
def eq_to_hom_f {P Q : karoubi C} (h : P = Q) :
  karoubi.hom.f (eq_to_hom h) = P.p ≫ eq_to_hom (congr_arg karoubi.X h) :=
by { subst h, simp only [eq_to_hom_refl, karoubi.id_eq, comp_id], }

end karoubi

@[simps]
def to_karoubi : C ⥤ karoubi C := {
  obj := λ X, ⟨X, 𝟙 X, by rw comp_id⟩,
  map := λ X Y f, ⟨f, by simp only [comp_id, id_comp]⟩ }

instance : full (to_karoubi C) := {
  preimage := λ X Y f', f'.1,
  witness' := λ X Y f', by { ext, simp only [to_karoubi_map_f], }, }

instance : faithful (to_karoubi C) := { }

variables {C}

@[simps]
instance {P Q : karoubi C} : add_comm_group (P ⟶ Q) :=
{ add := λ f' g', ⟨f'.1+g'.1, begin
    rw [add_comp, comp_add],
    congr',
    exact f'.2,
    exact g'.2,
  end⟩,
  zero := ⟨0, by simp only [comp_zero, zero_comp]⟩,
  zero_add := λ f', by { ext, simp only [zero_add], },
  add_zero := λ f', by { ext, simp only [add_zero], },
  add_assoc := λ f' g' h', by simp only [add_assoc],
  add_comm := λ f' g', by { ext, apply_rules [add_comm], },
  neg := λ f', ⟨-f'.1, by simpa only [neg_comp, comp_neg, neg_inj] using f'.2⟩,
  add_left_neg := λ f', by { ext, apply_rules [add_left_neg], }, }

namespace karoubi

lemma hom_eq_zero_iff {P Q : karoubi C} {f' : hom P Q} : f' = 0 ↔ f'.f = 0 := by tidy

@[simps]
def inclusion_hom (P Q : karoubi C) : add_monoid_hom (P ⟶ Q) (P.X ⟶ Q.X) :=
{ to_fun   := λ f', f'.1,
  map_zero' := rfl,
  map_add'  := λ f' g', rfl }

def sum_hom {P Q : karoubi C} {α : Type*} (s : finset α) (f : α → (P ⟶ Q)) :
  (∑ x in s, f x).1 = ∑ x in s, (f x).1  := 
add_monoid_hom.map_sum (inclusion_hom P Q) f s

end karoubi

instance : preadditive (karoubi C) :=
{ hom_group := λ P Q, by apply_instance,
  add_comp' := λ P Q R f' g' h',
    by { ext, simp only [add_comp, quiver.hom.add_comm_group_add_f, karoubi.comp], },
  comp_add' := λ P Q R f' g' h',
    by { ext, simp only [comp_add, quiver.hom.add_comm_group_add_f, karoubi.comp], }, }

instance : functor.additive (to_karoubi C) := { }


open karoubi

theorem karoubi_is_pseudoabelian : is_pseudoabelian (karoubi C) :=
{ idempotents_have_kernels := λ P, begin
    have h := P.idempotence,
    simp only [hom_ext, comp] at h,
    let Q : karoubi C := ⟨P.X.X, P.X.p - P.p.1,
      by { simp only [comp_sub, sub_comp, P.X.idempotence, p_comp, comp_p],
      simp only [comp_sub, sub_comp, P.X.idempotence,
        p_comp, comp_p, sub_zero, sub_self, h], }⟩,
    let ι : Q ⟶ P.X := ⟨P.X.p - P.p.1,
      by simp only [sub_comp, comp_sub, id_comp, p_comp, comp_p,
        P.X.idempotence, h, sub_zero, sub_self],⟩,
    exact { exists_limit :=
      ⟨{ cone := limits.kernel_fork.of_ι ι _, is_limit := _ }⟩ },
    { simp only [hom_eq_zero_iff, comp, sub_comp, p_comp, h, sub_self], },
    { refine is_limit.of_ι _ _ _ _ _,
      { intros W g hg,
        refine ⟨g.1, _⟩,
        simp only [hom_eq_zero_iff, comp] at hg,
        simp only [Q, comp_sub, comp, hg, comp_zero, sub_zero],
        exact g.2, },
      { intros W g hg,
        simp only [hom_eq_zero_iff, comp] at hg,
        simp only [comp, comp_sub, hom_ext, hg, sub_zero, comp_p], },
      { intros W g hg g' hg',
        simpa only [hom_eq_zero_iff, hom_ext, comp, comp_sub, comp_p] using hg', }, }
  end }

instance [is_pseudoabelian C] : ess_surj (to_karoubi C) := ⟨λ P,
begin
  let Q := idempotent_of_id_sub_idempotent P,
  let kernels := (show is_pseudoabelian C, by apply_instance).idempotents_have_kernels,
  haveI : has_kernel Q.p := kernels Q,
  have h := kernel.condition Q.p,
  simp only [idempotent_of_id_sub_idempotent_p, comp_sub, sub_eq_zero] at h,
  erw comp_id at h,  
  use kernel Q.p,
  apply nonempty.intro,
  refine
    { hom := ⟨kernel.ι Q.p, _⟩,
      inv := ⟨kernel.lift Q.p P.p _, _⟩,
      inv_hom_id' := _,
      hom_inv_id' := _, },
  /- hom is well defined -/
  { erw [← h, to_karoubi_obj_p, id_comp], },
  /- inv is well defined -/
  { simp only [comp_sub, idempotent_of_id_sub_idempotent_p, sub_eq_zero,
        P.idempotence], erw comp_id, },
  { slice_rhs 2 3 { erw [comp_id], },
    ext,
    simp only [assoc, kernel.lift_ι, P.idempotence], },
  /- inv_hom_id' -/
  { ext,
    simp only [equalizer_as_kernel, assoc, kernel.lift_ι,
      to_karoubi_obj_p, comp, assoc, id_eq],
    erw [← h, id_comp], },
  /- hom_inv_id' -/
  { simp only [comp, id_eq, kernel.lift_ι], },
end⟩

variables (C)

def karoubi_is_equivalence [is_pseudoabelian C] : is_equivalence (to_karoubi C) :=
  equivalence.of_fully_faithfully_ess_surj (to_karoubi C)

namespace karoubi

variables {C}

@[simps]
def decomp_id_i (P : karoubi C) : P ⟶ P.X := ⟨P.p, by erw [coe_p, comp_id, P.idempotence]⟩

@[simps]
def decomp_id_p (P : karoubi C) : (P.X : karoubi C) ⟶ P := ⟨P.p, by erw [coe_p, id_comp, P.idempotence]⟩

lemma decomp_id (P : karoubi C) :
  𝟙 P = (decomp_id_i P) ≫ (decomp_id_p P) :=
by { ext, simp only [comp, id_eq, P.idempotence, decomp_id_i, decomp_id_p], }


lemma decomp_p (P : karoubi C) :
  (to_karoubi C).map P.p = (decomp_id_p P) ≫ (decomp_id_i P) :=
by { ext, simp only [comp, decomp_id_p_f, decomp_id_i_f, P.idempotence, to_karoubi_map_f], }

def decomp_id_i_to_karoubi (X : C) : decomp_id_i ((to_karoubi C).obj X) = 𝟙 _ := by { ext, refl, }

def decomp_id_p_to_karoubi (X : C) : decomp_id_p ((to_karoubi C).obj X) = 𝟙 _ := by { ext, refl, }

def decomp_id_i_naturality {P Q : karoubi C} (f : P ⟶ Q) : f ≫ decomp_id_i _ =
  decomp_id_i _ ≫ ⟨f.f, by erw [comp_id, id_comp]⟩ :=
by { ext, simp only [comp, decomp_id_i_f, karoubi.comp_p, karoubi.p_comp], }

def decomp_id_p_naturality {P Q : karoubi C} (f : P ⟶ Q) : decomp_id_p P ≫ f =
  (⟨f.f, by erw [comp_id, id_comp]⟩ : (P.X : karoubi C) ⟶ Q.X) ≫ decomp_id_p Q :=
by { ext, simp only [comp, decomp_id_p_f, karoubi.comp_p, karoubi.p_comp], }

end karoubi

end pseudoabelian

end category_theory
