/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.preadditive
import category_theory.additive.basic
import category_theory.limits.shapes.biproducts
import category_theory.equivalence

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

namespace pseudoabelian

variables (C : Type*) [category C] [preadditive C]

structure karoubi := (X : C) (p : X ⟶ X) (idempotence : p ≫ p = p)

class is_pseudoabelian : Prop :=
(idempotents_have_kernels : Π (P : karoubi C), has_kernel P.p)

namespace karoubi

variables {C}

@[simps]
def idempotent_of_id_sub_idempotent (P : karoubi C) : karoubi C :=
{ X := P.X,
  p := 𝟙 _ - P.p,
  idempotence := by simp only [comp_sub, sub_comp, id_comp, comp_id, P.idempotence,
    sub_self, sub_zero], }

@[ext]
structure hom (P Q : karoubi C) := (f : P.X ⟶ Q.X) (comm : f = P.p ≫ f ≫ Q.p)

@[ext]
lemma hom_ext {P Q : karoubi C} {f' g' : hom P Q} : f' = g' ↔ f'.f = g'.f :=
by { split; intro h, { congr, assumption, }, { ext, assumption, }, }

@[simp]
def id (P : karoubi C) : hom P P := ⟨P.p, by repeat { rw P.idempotence, }⟩

lemma p_comp {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.1 = f.1 :=
by { rw [f.2, ← assoc, P.idempotence], }

lemma comp_p {P Q : karoubi C} (f : hom P Q) : f.1 ≫ Q.p = f.1 :=
by { rw [f.2, assoc, assoc, Q.idempotence], }

def comp_proof {P Q R : karoubi C} (g' : hom Q R) (f' : hom P Q) :
  f'.1 ≫ g'.1 = P.p ≫ (f'.1 ≫ g'.1) ≫ R.p :=
by rw [assoc, comp_p, ← assoc, p_comp]

@[simp]
def comp {P Q R : karoubi C} (g' : hom Q R) (f' : hom P Q) : hom P R :=
  ⟨f'.1 ≫ g'.1, comp_proof g' f'⟩

end karoubi

instance : category (karoubi C) :=
{ hom      := karoubi.hom,
  id       := karoubi.id,
  comp     := λ P Q R f' g', karoubi.comp g' f',
  id_comp' := λ P Q f', by { ext, simp only [karoubi.id, karoubi.comp, karoubi.p_comp], },
  comp_id' := λ P Q f', by { ext, simp only [karoubi.id, karoubi.comp, karoubi.comp_p], },
  assoc'   := λ P Q R S f' g' h', by { ext, simp only [category.assoc, karoubi.comp], }, }

namespace karoubi

@[simp]
lemma comp_eq {P Q R : karoubi C} (f' : P ⟶ Q) (g' : Q ⟶ R) :
  f' ≫ g' = ⟨f'.1 ≫ g'.1, comp_proof g' f'⟩ := by refl

@[simp]
lemma id_eq {P : karoubi C} : 𝟙 P = ⟨P.p, by repeat { rw P.idempotence, }⟩ := by refl

instance coe : has_coe C (karoubi C) := ⟨λ X, ⟨X, 𝟙 X, by rw comp_id⟩⟩

@[simp]
lemma coe_X (X : C) : (X : karoubi C).X = X := by refl

@[simp]
lemma coe_p (X : C) : (X : karoubi C).p = 𝟙 X := by refl

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

@[simp]
lemma add_hom {P Q : karoubi C} (f' g' : P ⟶ Q) : f' + g' = ⟨f'.1+g'.1,
  by { rw [add_comp, comp_add], congr', exact f'.2, exact g'.2, }⟩ := by refl

@[simp]
lemma zero_eq {P Q : karoubi C} : (0 : P ⟶ Q) = ⟨0, by simp only [comp_zero, zero_comp]⟩ := by refl

lemma hom_eq_zero_iff {P Q : karoubi C} {f' : hom P Q} : f' = 0 ↔ f'.f = 0 :=
begin
  split; intro h,
  { rw [h, zero_eq], },
  { ext,
    rw [h, zero_eq], }
end

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
  add_comp' := λ P Q R f' g' h', by { simp only [karoubi.add_hom, karoubi.comp_eq, add_comp], },
  comp_add' := λ P Q R f' g' h', by { simp only [karoubi.add_hom, karoubi.comp_eq, comp_add], }, }

namespace karoubi

namespace biproducts

variables {C}
variables {J : Type*} [decidable_eq J] [fintype J] (F : J → karoubi C)
variables [has_finite_biproducts C]

abbreviation biconeX := biproduct.bicone (λ j, (F j).X)

abbreviation biconeX_p := biproduct.map (λ j, (F j).p)

lemma biconeX_p_idempotence : biconeX_p F ≫ biconeX_p F = biconeX_p F :=
begin
  ext j,
  simp only [limits.biproduct.ι_map_assoc, limits.biproduct.ι_map],
  slice_lhs 1 2 { rw (F j).idempotence, },
end

@[simps]
def bicone : limits.bicone F :=
{ X :=
  { X := (biconeX F).X,
    p := (biconeX_p F),
      idempotence := biconeX_p_idempotence F, },
  π := λ j, ⟨biconeX_p F ≫ (biconeX F).π j,
    by { simp only [limits.biproduct.map_π_assoc, category.assoc,
      limits.biproduct.map_π, (F j).idempotence], }⟩,
  ι := λ j, ⟨(biconeX F).ι j ≫ biconeX_p F,
    by { simp only [limits.biproduct.ι_map, category.assoc],
      slice_rhs 1 3 { rw [(F j).idempotence, (F j).idempotence], }, }⟩,
  ι_π := λ j j', begin
    split_ifs,
    { subst h,
      simp only [limits.biproduct.bicone_ι, limits.biproduct.ι_map,
        limits.biproduct.bicone_π, limits.biproduct.ι_π_self_assoc,
        karoubi.comp_eq, category.assoc, eq_to_hom_refl,
      limits.biproduct.map_π, karoubi.id_eq, (F j).idempotence], },
    { simp only [karoubi.comp_eq],
      conv { to_lhs, congr, rw assoc, congr, skip, rw ← assoc, congr,
        rw biconeX_p_idempotence, },
      simp only [limits.biproduct.bicone_ι, limits.biproduct.bicone_π,
        limits.biproduct.map_π],
      conv { to_lhs, congr, rw ← assoc, congr, rw (biconeX F).ι_π, },
      split_ifs,
      simp only [zero_comp, karoubi.zero_eq], },
  end, }

end biproducts

instance [has_finite_biproducts C] : has_finite_biproducts (karoubi C) :=
{ has_biproducts_of_shape := λ J hJ1 hJ2,
  { has_biproduct := λ F, begin
      letI := hJ2,
      apply has_biproduct_of_total (biproducts.bicone F),
      ext1, ext1,
      simp only [karoubi.id_eq, comp_id, biproducts.bicone_X_p,
        limits.biproduct.ι_map],
      rw [sum_hom, comp_sum],
      rw finset.sum_eq_single j, rotate,
      { intros j' h1 h2,
        simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f, assoc, comp_eq, biproduct.map_π],
        slice_lhs 1 2 { rw biproduct.ι_π, },
        split_ifs,
        { exfalso, exact h2 h.symm, },
        { simp only [zero_comp], } },
      { intro h1,
        exfalso,
        simpa only [finset.mem_univ, not_true] using h1, },
      simp only [biproducts.bicone_π_f, comp_eq,
        biproduct.ι_map, assoc, biproducts.bicone_ι_f, biproduct.map_π],
      slice_lhs 1 2 { rw biproduct.ι_π, },
      split_ifs, swap, { exfalso, exact h rfl, },
      simp only [eq_to_hom_refl, id_comp, (F j).idempotence],
    end, } }

end karoubi

theorem karoubi_is_pseudoabelian : is_pseudoabelian (karoubi C) :=
{ idempotents_have_kernels := λ P, begin
    have h := P.idempotence,
    simp only [karoubi.hom_ext, karoubi.comp_eq] at h,
    let Q : karoubi C := ⟨P.X.X, P.X.p - P.p.1,
      by { simp only [comp_sub, sub_comp, P.X.idempotence, karoubi.p_comp,
        karoubi.comp_p],
      simp only [comp_sub, sub_comp, P.X.idempotence,
      karoubi.p_comp, karoubi.comp_p, sub_zero, sub_self, h], }⟩,
    let ι : Q ⟶ P.X := ⟨P.X.p - P.p.1,
      by simp only [sub_comp, comp_sub, id_comp, karoubi.p_comp, karoubi.comp_p,
        P.X.idempotence, h, sub_zero, sub_self],⟩,
    refine { exists_limit :=
      ⟨{ cone := limits.kernel_fork.of_ι ι _, is_limit := _ }⟩ },
    { simp only [karoubi.zero_eq, karoubi.comp_eq, sub_comp,
          karoubi.p_comp, h, sub_self], },
    { refine is_limit.of_ι _ _ _ _ _,
      { intros W g hg,
        refine ⟨g.1, _⟩,
        simp only [karoubi.hom_eq_zero_iff, karoubi.comp_eq] at hg,
        simp only [Q, comp_sub, karoubi.comp_eq, hg, comp_zero, sub_zero],
        exact g.2, },
      { intros W g hg,
        simp only [karoubi.hom_ext, karoubi.comp_eq, karoubi.zero_eq, comp_sub] at hg ⊢,
        simp only [hg, sub_zero, karoubi.comp_p], },
      { intros W g hg g' hg',
        simpa only [karoubi.hom_ext, karoubi.comp_eq, karoubi.zero_eq,
          comp_sub, karoubi.comp_p] using hg', }, }      
  end }

instance [is_pseudoabelian C] : ess_surj (to_karoubi C) := ⟨λ P,
begin
  let Q := karoubi.idempotent_of_id_sub_idempotent P,
  let kernels := (show is_pseudoabelian C, by apply_instance).idempotents_have_kernels,
  haveI : has_kernel Q.p := kernels Q,
  have h := kernel.condition Q.p,
  simp only [karoubi.idempotent_of_id_sub_idempotent_p, comp_sub, sub_eq_zero] at h,
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
  { simp only [comp_sub, karoubi.idempotent_of_id_sub_idempotent_p, sub_eq_zero,
        P.idempotence], erw comp_id, },
  { slice_rhs 2 3 { erw [comp_id], },
    ext,
    simp only [assoc, kernel.lift_ι, P.idempotence], },
  /- inv_hom_id' -/
  { ext,
    simp only [equalizer_as_kernel, assoc, kernel.lift_ι,
      to_karoubi_obj_p, karoubi.comp_eq, assoc, karoubi.id_eq],
    erw [← h, id_comp], },
  /- hom_inv_id' -/
  { simp only [karoubi.comp_eq, karoubi.id_eq, kernel.lift_ι], },
end⟩

variables (C)

def karoubi_is_equivalence [is_pseudoabelian C] : is_equivalence (to_karoubi C) :=
  equivalence.of_fully_faithfully_ess_surj (to_karoubi C)

namespace karoubi

variables {C}

@[simps]
def functor_extension {D: Type*} [category D] [preadditive D]
  (F : C ⥤ D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨F.obj P.X, F.map P.p, 
    by { rw ← F.map_comp, congr, exact P.idempotence, }⟩,
  map := λ P Q f, ⟨F.map f.1,
    by { simp only [← F.map_comp], congr, exact f.2, }⟩, }

@[simps]
def functor_extension' {D: Type*} [category D] [preadditive D]
  (F : C ⥤ karoubi D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).1, begin
    have h := congr_arg (λ (f : P.X ⟶ P.X), F.map f) P.idempotence,
    simpa only [F.map_comp, karoubi.hom_ext, karoubi.comp_eq] using h,
  end⟩,
  map := λ P Q f, ⟨(F.map f.1).1, begin
    have h := congr_arg (λ (f : P.X ⟶ Q.X), F.map f) f.2,
    simpa only [F.map_comp, karoubi.hom_ext, karoubi.comp_eq] using h,
  end⟩, }

@[simp]
def functor_extension'' {D: Type*} [category D] [preadditive D] [is_pseudoabelian D]
  (F : C ⥤ D) : karoubi C ⥤ D :=
  functor_extension F ⋙ (karoubi_is_equivalence D).inverse

end karoubi

namespace karoubi_karoubi

def inverse : karoubi (karoubi C) ⥤ karoubi C :=
  { obj := λ P, ⟨P.X.X, P.p.1,
      by simpa only [karoubi.hom_ext, karoubi.comp_eq] using P.idempotence⟩,
    map := λ P Q f, ⟨f.1.1,
      by simpa only [karoubi.hom_ext, karoubi.comp_eq] using f.2⟩, }

def unit_iso : 𝟭 (karoubi C) ≅ to_karoubi (karoubi C) ⋙ karoubi_karoubi.inverse C :=
{ hom :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f,
      by { cases P, cases Q, cases f, dsimp [karoubi_karoubi.inverse],
        simp only [comp_id, id_comp, karoubi.hom_ext], }, },
  inv :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f, begin
      cases P,
      cases Q,
      dsimp [karoubi_karoubi.inverse],
      simp only [karoubi.comp_eq, comp_id, id_comp, karoubi.hom_ext],
    end },
  hom_inv_id' := begin
    ext P,
    cases P,
    dsimp,
    simp only [karoubi.comp_eq, karoubi.id_eq, karoubi.hom_ext],
    simpa using P_idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    cases P,
    dsimp,
    simp only [karoubi.comp_eq, karoubi.id_eq, karoubi.hom_ext],
    simpa using P_idempotence,
  end, }

def counit_iso : karoubi_karoubi.inverse C ⋙ to_karoubi (karoubi C) ≅ 𝟭 (karoubi (karoubi C)) :=
{ hom := 
  { app := λ P, ⟨⟨P.p.1, begin
    have h := P.idempotence,
    simp only [karoubi.hom_ext, karoubi.comp_eq] at h,
    erw [← assoc, h, karoubi.comp_p],
    end⟩,
    begin
      have h := P.idempotence,
      simp only [karoubi.hom_ext, karoubi.comp_eq] at h ⊢,
      erw [h, h],
    end⟩,
    naturality' := λ P Q f, begin
      have h := karoubi.comp_p f,
      have h' := karoubi.p_comp f,
      simp only [karoubi.hom_ext, karoubi.comp_eq] at h h' ⊢,
      erw [h, h'],
    end, },
  inv :=
  { app := λ P, ⟨⟨P.p.1, begin
      have h := P.idempotence,
      simp only [karoubi.hom_ext, karoubi.comp_eq] at h,
      erw [h, karoubi.p_comp],
    end⟩,
    begin
      have h := P.idempotence,
      simp only [karoubi.hom_ext, karoubi.comp_eq] at h ⊢,
      erw [h, h],
    end⟩,
    naturality' := λ P Q f, begin
      have h := karoubi.comp_p f,
      have h' := karoubi.p_comp f,
      simp only [karoubi.hom_ext, karoubi.comp_eq] at h h' ⊢,
      erw [h, h'],
    end, },
  hom_inv_id' := begin
    ext P,
    dsimp,
    simpa only [karoubi.hom_ext, karoubi.comp_eq, karoubi.id_eq] using P.idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    dsimp,
    simpa only [karoubi.hom_ext, karoubi.comp_eq, karoubi.id_eq] using P.idempotence,
  end, }

end karoubi_karoubi

def karoubi_karoubi : karoubi C ≌ karoubi (karoubi C) :=
{ functor := to_karoubi (karoubi C),
  inverse := karoubi_karoubi.inverse C,
  unit_iso := karoubi_karoubi.unit_iso C,
  counit_iso := karoubi_karoubi.counit_iso C,
  functor_unit_iso_comp' := λ P, begin
    cases P,
    dsimp [karoubi_karoubi.unit_iso, karoubi_karoubi.counit_iso, to_karoubi],
    simp only [karoubi.comp_eq, karoubi.id_eq, subtype.coe_mk, P_idempotence],
  end, }
end pseudoabelian

end category_theory
