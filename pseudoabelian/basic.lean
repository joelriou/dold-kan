/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.preadditive.additive_functor
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

@[nolint has_inhabited_instance]
structure karoubi := (X : C) (p : X ⟶ X) (idempotence : p ≫ p = p)

class is_pseudoabelian : Prop :=
(idempotents_have_kernels : Π (P : karoubi C), has_kernel P.p)

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
        comp, category.assoc, eq_to_hom_refl,
      limits.biproduct.map_π, id_eq, (F j).idempotence], },
    { simp only [comp],
      conv { to_lhs, congr, rw assoc, congr, skip, rw ← assoc, congr,
        rw biconeX_p_idempotence, },
      simp only [limits.biproduct.bicone_ι, limits.biproduct.bicone_π,
        limits.biproduct.map_π],
      conv { to_lhs, congr, rw ← assoc, congr, rw (biconeX F).ι_π, },
      split_ifs,
      simp only [hom_eq_zero_iff, zero_comp], },
  end, }

end biproducts

instance [has_finite_biproducts C] : has_finite_biproducts (karoubi C) :=
{ has_biproducts_of_shape := λ J hJ1 hJ2,
  { has_biproduct := λ F, begin
      letI := hJ2,
      apply has_biproduct_of_total (biproducts.bicone F),
      ext1, ext1,
      simp only [id_eq, comp_id, biproducts.bicone_X_p,
        limits.biproduct.ι_map],
      rw [sum_hom, comp_sum],
      rw finset.sum_eq_single j, rotate,
      { intros j' h1 h2,
        simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f, assoc, comp, biproduct.map_π],
        slice_lhs 1 2 { rw biproduct.ι_π, },
        split_ifs,
        { exfalso, exact h2 h.symm, },
        { simp only [zero_comp], } },
      { intro h1,
        exfalso,
        simpa only [finset.mem_univ, not_true] using h1, },
      simp only [biproducts.bicone_π_f, comp,
        biproduct.ι_map, assoc, biproducts.bicone_ι_f, biproduct.map_π],
      slice_lhs 1 2 { rw biproduct.ι_π, },
      split_ifs, swap, { exfalso, exact h rfl, },
      simp only [eq_to_hom_refl, id_comp, (F j).idempotence],
    end, } }

end karoubi

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
    refine { exists_limit :=
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
def functor_extension {D : Type*} [category D] [preadditive D]
  (F : C ⥤ D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨F.obj P.X, F.map P.p, 
    by { rw ← F.map_comp, congr, exact P.idempotence, }⟩,
  map := λ P Q f, ⟨F.map f.1,
    by { simp only [← F.map_comp], congr, exact f.2, }⟩, }

@[simps]
def functor_extension' {D : Type*} [category D] [preadditive D]
  (F : C ⥤ karoubi D) : karoubi C ⥤ karoubi D :=
{ obj := λ P, ⟨(F.obj P.X).X, (F.map P.p).1, begin
    have h := congr_arg (λ (f : P.X ⟶ P.X), F.map f) P.idempotence,
    simpa only [F.map_comp, hom_ext] using h,
  end⟩,
  map := λ P Q f, ⟨(F.map f.1).1, begin
    have h := congr_arg (λ (f : P.X ⟶ Q.X), F.map f) f.2,
    simpa only [F.map_comp, hom_ext] using h,
  end⟩, }

@[simp]
def functor_extension'' {D : Type*} [category D] [preadditive D] [is_pseudoabelian D]
  (F : C ⥤ D) : karoubi C ⥤ D :=
  functor_extension F ⋙ (karoubi_is_equivalence D).inverse

abbreviation decomp_id_i (P : karoubi C) : P ⟶ P.X := ⟨P.p, by erw [coe_p, comp_id, P.idempotence]⟩
abbreviation decomp_id_p (P : karoubi C) : (P.X : karoubi C) ⟶ P := ⟨P.p, by erw [coe_p, id_comp, P.idempotence]⟩

lemma decomp_id (P : karoubi C) :
  𝟙 P = (decomp_id_i P) ≫ (decomp_id_p P) :=
by { ext, simp only [comp, id_eq, P.idempotence], }

def nat_trans_eq {D : Type*} [category D] {F G : karoubi C ⥤ D} (φ : F ⟶ G) (P : karoubi C) :
  φ.app P = F.map (⟨P.p, by erw [coe_p, comp_id, P.idempotence]⟩ : P ⟶ P.X) ≫ φ.app P.X
    ≫ G.map (⟨P.p, by erw [coe_p, id_comp, P.idempotence]⟩) :=
begin
  rw [← φ.naturality, ← assoc, ← F.map_comp],
  conv { to_lhs, rw [← id_comp (φ.app P), ← F.map_id], },
  congr,
  apply decomp_id,
end

@[simps]
def functor_extension_hom_equiv {D : Type*} [category D] [preadditive D]
  (F G : C ⥤ D) : (F ⟶ G) ≃ (functor_extension F ⟶ functor_extension G) :=
{ to_fun := λ φ,
  { app := λ P,
    { f := F.map P.p ≫ φ.app P.X ≫ G.map P.p,
      comm := begin
        simp only [functor_extension_obj_p],
        slice_rhs 1 2 { rw [← F.map_comp, P.idempotence], },
        slice_rhs 3 4 { rw [← G.map_comp, P.idempotence], },
      end },
    naturality' := λ P Q f, begin
      ext,
      simp only [functor_extension_map_f, comp, assoc, nat_trans.naturality_assoc],
      simp only [← G.map_comp, karoubi.p_comp, ← assoc, karoubi.comp_p],
    end },
  inv_fun := λ ψ,
  { app := λ X, (ψ.app ((to_karoubi C).obj X)).f,
    naturality' := λ X Y f, hom_ext.mp (ψ.naturality ((to_karoubi C).map f)), },
  left_inv := λ φ, begin
    ext X,
    dsimp,
    simp only [functor.map_id, id_comp, comp_id],
  end,
  right_inv := λ ψ, begin
    ext1,
    ext1 P,
    exact (nat_trans_eq ψ P).symm,
  end } 

lemma functor_extension_hom_to_fun_comp {D : Type*} [category D] [preadditive D]
  {F G H : C ⥤ D} (φ : F ⟶ G) (ψ : G ⟶ H) :
  (functor_extension_hom_equiv F H).to_fun (φ ≫ ψ) =
  (functor_extension_hom_equiv F G).to_fun φ ≫ (functor_extension_hom_equiv G H).to_fun ψ :=
begin
  ext P,
  simp only [equiv.to_fun_as_coe, functor_extension_hom_equiv_apply_app_f, comp,
    assoc, nat_trans.naturality_assoc, nat_trans.comp_app, ← H.map_comp, P.idempotence],
end

lemma functor_extension_hom_to_fun_id {D : Type*} [category D] [preadditive D]
  {F : C ⥤ D} :
  (functor_extension_hom_equiv F F).to_fun (𝟙 F) = 𝟙 _ :=
begin
  ext P,
  simp only [equiv.to_fun_as_coe, functor_extension_hom_equiv_apply_app_f, id_eq,
    nat_trans.id_app, functor_extension_obj_p, id_comp, ← F.map_comp, P.idempotence],
end

lemma functor_extension_hom_inv_fun_comp {D : Type*} [category D] [preadditive D]
  {F G H : C ⥤ D} (φ : functor_extension F ⟶ functor_extension G) (ψ : functor_extension G ⟶ functor_extension H) :
  (functor_extension_hom_equiv F H).inv_fun (φ ≫ ψ) =
  (functor_extension_hom_equiv F G).inv_fun φ ≫ (functor_extension_hom_equiv G H).inv_fun ψ :=
begin
  ext X,
  simp only [comp, nat_trans.comp_app, equiv.inv_fun_as_coe,
    functor_extension_hom_equiv_symm_apply_app],
end

lemma functor_extension_hom_inv_fun_id {D : Type*} [category D] [preadditive D]
  {F : C ⥤ D} :
  (functor_extension_hom_equiv F F).inv_fun (𝟙 (functor_extension F)) = 𝟙 _ :=
begin
  ext X,
  simp only [to_karoubi_obj_p, id_eq, nat_trans.id_app, functor_extension_obj_p,
    equiv.inv_fun_as_coe, functor_extension_hom_equiv_symm_apply_app, F.map_id X],
end

@[simps]
def functor_extension_iso_equiv {D : Type*} [category D] [preadditive D]
  (F : C ⥤ D) (G : C ⥤ D) : (F ≅ G) ≃ (functor_extension F ≅ functor_extension G) :=
{ to_fun := λ φ,
  { hom := (functor_extension_hom_equiv F G).to_fun φ.hom,
    inv := (functor_extension_hom_equiv G F).to_fun φ.inv,
    hom_inv_id' := by rw [← functor_extension_hom_to_fun_comp, φ.hom_inv_id, functor_extension_hom_to_fun_id],
    inv_hom_id' := by rw [← functor_extension_hom_to_fun_comp, φ.inv_hom_id, functor_extension_hom_to_fun_id], },
  inv_fun := λ ψ,
  { hom := (functor_extension_hom_equiv F G).inv_fun ψ.hom,
    inv := (functor_extension_hom_equiv G F).inv_fun ψ.inv,
    hom_inv_id' := by rw [← functor_extension_hom_inv_fun_comp, ψ.hom_inv_id, functor_extension_hom_inv_fun_id],
    inv_hom_id' := by rw [← functor_extension_hom_inv_fun_comp, ψ.inv_hom_id, functor_extension_hom_inv_fun_id], },
  left_inv := λ φ, by { ext1, exact (functor_extension_hom_equiv F G).left_inv φ.hom, },
  right_inv := λ ψ, by { ext1, exact (functor_extension_hom_equiv F G).right_inv ψ.hom, }, }

end karoubi

namespace karoubi_karoubi

@[simps]
def inverse : karoubi (karoubi C) ⥤ karoubi C :=
  { obj := λ P, ⟨P.X.X, P.p.1,
      by simpa only [hom_ext] using P.idempotence⟩,
    map := λ P Q f, ⟨f.1.1,
      by simpa only [hom_ext] using f.2⟩, }

instance : functor.additive (inverse C) := { }

@[simps]
def unit_iso : 𝟭 (karoubi C) ≅ to_karoubi (karoubi C) ⋙ inverse C :=
{ hom :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f,
      by { cases P, cases Q, cases f, dsimp [inverse],
        simp only [comp_id, id_comp, hom_ext], }, },
  inv :=
  { app := λ P, eq_to_hom (by { cases P, refl, }),
    naturality' := λ P Q f, begin
      cases P,
      cases Q,
      dsimp [inverse],
      simp only [comp_id, id_comp, hom_ext],
    end },
  hom_inv_id' := begin
    ext P,
    cases P,
    dsimp,
    simpa only [id_eq, hom_ext] using P_idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    cases P,
    dsimp,
    simpa only [id_eq, hom_ext] using P_idempotence,
  end, }

@[simps]
def counit_iso : inverse C ⋙ to_karoubi (karoubi C) ≅ 𝟭 (karoubi (karoubi C)) :=
{ hom := 
  { app := λ P, ⟨⟨P.p.1, begin
    have h := P.idempotence,
    simp only [hom_ext, comp] at h,
    erw [← assoc, h, comp_p],
    end⟩,
    begin
      have h := P.idempotence,
      simp only [hom_ext, comp] at h ⊢,
      erw [h, h],
    end⟩,
    naturality' := λ P Q f, begin
      have h := comp_p f,
      have h' := p_comp f,
      simp only [hom_ext] at h h' ⊢,
      erw [h, h'],
    end, },
  inv :=
  { app := λ P, ⟨⟨P.p.1, begin
      have h := P.idempotence,
      simp only [hom_ext, comp] at h,
      erw [h, p_comp],
    end⟩,
    begin
      have h := P.idempotence,
      simp only [hom_ext, comp] at h ⊢,
      erw [h, h],
    end⟩,
    naturality' := λ P Q f, begin
      have h := comp_p f,
      have h' := p_comp f,
      simp only [hom_ext] at h h' ⊢,
      erw [h, h'],
    end, },
  hom_inv_id' := begin
    ext P,
    dsimp,
    simpa only [hom_ext, id_eq] using P.idempotence,
  end,
  inv_hom_id' := begin
    ext P,
    dsimp,
    simpa only [hom_ext, id_eq] using P.idempotence,
  end, }

end karoubi_karoubi

@[simps]
def karoubi_karoubi_equivalence : karoubi C ≌ karoubi (karoubi C) :=
{ functor := to_karoubi (karoubi C),
  inverse := karoubi_karoubi.inverse C,
  unit_iso := karoubi_karoubi.unit_iso C,
  counit_iso := karoubi_karoubi.counit_iso C,
  functor_unit_iso_comp' := λ P, begin
    cases P,
    dsimp [karoubi_karoubi.unit_iso, karoubi_karoubi.counit_iso, to_karoubi],
    simp only [comp, id_eq, subtype.coe_mk, P_idempotence],
  end, }

instance : functor.additive (karoubi_karoubi_equivalence C).functor :=
  by { dsimp, apply_instance, }

instance : functor.additive (karoubi_karoubi_equivalence C).inverse :=
  by { dsimp, apply_instance, }

end pseudoabelian

end category_theory

