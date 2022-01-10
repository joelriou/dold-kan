/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.preadditive
import category_theory.additive.basic
import category_theory.limits.shapes.biproducts

/-!
# Pseudoabelian categories

-/

open category_theory
open category_theory.category
open category_theory.limits

noncomputable theory

open category_theory
open category_theory.preadditive

namespace category_theory

namespace pseudoabelian

variables {C : Type*} [category C] [preadditive C]
variable {X : C}

class projector (p : X ⟶ X) : Prop := (idempotence : p ≫ p = p)

@[simp]
def binary_bicone_of_projector {X : C} (p : X ⟶ X)
  [h : projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
  binary_bicone (kernel (𝟙 X - p)) (kernel p) :=
{ X := X,
  inl := kernel.ι (𝟙 X - p),
  inr := kernel.ι p,
  fst := kernel.lift (𝟙 X - p) p 
    (by { rw [comp_sub, category.comp_id, sub_eq_zero], exact h.idempotence.symm, }),
  snd := kernel.lift p (𝟙 X - p)
    (by { rw [sub_comp, category.id_comp, sub_eq_zero], exact h.idempotence.symm, }),
  inl_snd' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
    assoc, kernel.lift_ι], },
  inr_fst' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
    assoc, kernel.lift_ι], },
  inl_fst' :=
  begin
    ext,
    rw [assoc, limits.kernel.lift_ι, limits.equalizer_as_kernel, id_comp],
    symmetry,
    conv { to_lhs, rw ← comp_id (kernel.ι _), },
    apply sub_eq_zero.mp,
    rw [← comp_sub, kernel.condition],
  end,
  inr_snd' := by { ext, rw [assoc, kernel.lift_ι, equalizer_as_kernel, id_comp, comp_sub,
      kernel.condition, sub_zero, comp_id], }, }

def binary_biproduct_data_of_projector {X : C} (p : X ⟶ X)
  [h : projector p] [has_kernel p] [has_kernel (𝟙 X - p)] :
  binary_biproduct_data (kernel (𝟙 X - p)) (kernel p) :=
  binary_biproduct_data_of_total
  { X := X,
    inl := kernel.ι (𝟙 X - p),
    inr := kernel.ι p,
    fst := kernel.lift (𝟙 X - p) p 
      (by { rw [comp_sub, category.comp_id, sub_eq_zero], exact h.idempotence.symm, }),
    snd := kernel.lift p (𝟙 X - p)
      (by { rw [sub_comp, category.id_comp, sub_eq_zero], exact h.idempotence.symm, }),
    inl_snd' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
      assoc, kernel.lift_ι], },
    inr_fst' := by { dsimp, ext, simp only [zero_comp, kernel.condition,
      assoc, kernel.lift_ι], },
    inl_fst' :=
    begin
      ext,
      rw [assoc, limits.kernel.lift_ι, limits.equalizer_as_kernel, id_comp],
      symmetry,
      conv { to_lhs, rw ← comp_id (kernel.ι _), },
      apply sub_eq_zero.mp,
      rw [← comp_sub, kernel.condition],
    end,
    inr_snd' := by { ext, rw [assoc, kernel.lift_ι, equalizer_as_kernel, id_comp, comp_sub,
        kernel.condition, sub_zero, comp_id], }, }
  (by { dsimp [binary_bicone_of_projector], simp only [kernel.lift_ι, add_sub_cancel'_right], })

class is_pseudoabelian : Prop :=
(projectors_have_kernels : Π (X : C) (p : X ⟶ X), projector p → has_kernel p)

variables (C)

structure karoubi := (X : C) (p : X ⟶ X) (idempotence : p ≫ p = p)

namespace karoubi

variables {C}

def hom (P Q : karoubi C) := { f : P.X ⟶ Q.X // f = P.p ≫ f ≫ Q.p }

@[ext]
lemma hom_ext {P Q : karoubi C} (f' g' : hom P Q) : f'.1 = g'.1 → f' = g' :=
by { intro h, cases f', cases g', simpa only [subtype.mk_eq_mk] using h, }

@[simp]
def id (P : karoubi C) : hom P P := ⟨P.p, by repeat { rw P.idempotence, }⟩

lemma comp_p {P Q : karoubi C} (f : hom P Q) : P.p ≫ f.1 = f.1 :=
by { rw [f.2, ← assoc, P.idempotence], }

lemma p_comp {P Q : karoubi C} (f : hom P Q) : f.1 ≫ Q.p = f.1 :=
by { rw [f.2, assoc, assoc, Q.idempotence], }

def comp_proof {P Q R : karoubi C} (g' : hom Q R) (f' : hom P Q) :
  f'.1 ≫ g'.1 = P.p ≫ (f'.1 ≫ g'.1) ≫ R.p :=
by rw [assoc, p_comp, ← assoc, comp_p]

@[simp]
def comp {P Q R : karoubi C} (g' : hom Q R) (f' : hom P Q) : hom P R :=
  ⟨f'.1 ≫ g'.1, comp_proof g' f'⟩

end karoubi

instance : category (karoubi C) :=
{ hom      := karoubi.hom,
  id       := karoubi.id,
  comp     := λ P Q R f' g', karoubi.comp g' f',
  id_comp' := λ P Q f', by { ext, simp only [karoubi.id, karoubi.comp, karoubi.comp_p], },
  comp_id' := λ P Q f', by { ext, simp only [karoubi.id, karoubi.comp, karoubi.p_comp], },
  assoc'   := λ P Q R S f' g' h', by { ext, simp only [category.assoc, karoubi.comp], }, }

namespace karoubi

@[simp]
lemma comp_def {P Q R : karoubi C} (f' : P ⟶ Q) (g' : Q ⟶ R) :
  f' ≫ g' = ⟨f'.1 ≫ g'.1, comp_proof g' f'⟩ := by refl

@[simp]
lemma id_def {P : karoubi C} : 𝟙 P = ⟨P.p, by repeat { rw P.idempotence, }⟩ := by refl

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
  witness' := λ X Y f', by { ext, simp only [to_karoubi_map_coe, subtype.val_eq_coe], }, }

instance : faithful (to_karoubi C) := { }

instance {P Q : karoubi C} : add_comm_group (P ⟶ Q) := {
  add := λ f' g', ⟨f'.1+g'.1, begin
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
lemma zero_def {P Q : karoubi C} : (0 : P ⟶ Q) = ⟨0, by simp only [comp_zero, zero_comp]⟩ := by refl

end karoubi

instance : preadditive (karoubi C) :=
{ hom_group := λ P Q, by apply_instance,
  add_comp' := λ P Q R f' g' h', by { simp only [karoubi.add_hom, karoubi.comp_def, add_comp], },
  comp_add' := λ P Q R f' g' h', by { simp only [karoubi.add_hom, karoubi.comp_def, comp_add], }, }

instance [has_finite_biproducts C] : has_finite_biproducts (karoubi C) :=
{ has_biproducts_of_shape := λ J hJ1 hJ2,
  { has_biproduct := λ F,
    { exists_biproduct := begin
        apply nonempty.intro,
        letI := hJ1,
        let biconeX := biproduct.bicone (λ j, (F j).X),
        let biconeX_p := biproduct.map (λ j, (F j).p), 
        have biconeX_p_idempotence : biconeX_p ≫ biconeX_p = biconeX_p,
        { ext j,
          simp only [limits.biproduct.ι_map_assoc, limits.biproduct.ι_map],
         slice_lhs 1 2 { rw (F j).idempotence, }, },
        exact {
          bicone := {
            X :=
            { X := biconeX.X,
              p := biconeX_p,
              idempotence := biconeX_p_idempotence, },
            π := λ j, ⟨biconeX_p ≫ biconeX.π j,
              by { simp only [limits.biproduct.map_π_assoc, category.assoc,
                limits.biproduct.map_π, (F j).idempotence], }⟩,
            ι := λ j, ⟨biconeX.ι j ≫ biconeX_p,
              by { simp only [limits.biproduct.ι_map, category.assoc],
                slice_rhs 1 3 { rw [(F j).idempotence, (F j).idempotence], }, }⟩,
            ι_π := λ j j', begin
              split_ifs,
              { subst h,
                simp only [limits.biproduct.bicone_ι, limits.biproduct.ι_map,
                  limits.biproduct.bicone_π, limits.biproduct.ι_π_self_assoc,
                  karoubi.comp_def, category.assoc, eq_to_hom_refl,
                  limits.biproduct.map_π, karoubi.id_def, (F j).idempotence], },
              { simp only [karoubi.comp_def],
                conv { to_lhs, congr, rw assoc, congr, skip, rw ← assoc, congr,rw biconeX_p_idempotence, },
                simp only [limits.biproduct.bicone_ι, limits.biproduct.bicone_π, limits.biproduct.map_π],
                conv { to_lhs, congr, rw ← assoc, congr, rw biconeX.ι_π, },
                split_ifs,
                simp only [zero_comp, karoubi.zero_def], }
            end,
          },
          is_limit := sorry,
          is_colimit := sorry, },
      end, }, }, }


--instance [additive_category C] : additive_category (karoubi C) := { }


end pseudoabelian

end category_theory

/-!
 additive_category si C l'est
 pseudoab
 to_karoubi est une equiv sssi C est pseudoab -/

