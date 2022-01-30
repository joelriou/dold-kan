import category_theory.additive.basic
import category_theory.limits.shapes.images
import data.sigma.basic
import data.fintype.basic
import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import simplex_category

import dold_kan4

/-!

Goal : 
* check that this gives the expected equivalence of categories (TODO)

-/

universes v u

open classical
noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite
open_locale simplicial
open category_theory.pseudoabelian

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category.{v} C] [additive_category C]

@[simps]
def ΓN'_trans : N' ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _)
  ⟶ to_karoubi _ :=
{ app := λ X,
  { f := -- il faut mettre P_infty dans le définition...
    { app := λ Δ, sigma.desc (λ A, X.map
        (eq_to_hom (by { simp only [simplex_category.mk_len], }) ≫ A.2.1.op)),
      naturality' := sorry, },
    comm := sorry },
  naturality' := λ X Y f, begin
    ext Δ A,
    sorry,
  end }

@[simps]
def ΓN_trans : N ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _)
  ⟶ 𝟭 _ :=
((karoubi.to_karoubi_hom_equiv
    (N ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _)) (𝟭 _)).inv_fun)
    ((eq_to_hom (by { rw ← karoubi.to_karoubi_comp_functor_extension' N', refl, }))
    ≫ ΓN'_trans ≫ eq_to_hom (functor.comp_id _).symm)

lemma identity_N : ((𝟙 (N : karoubi (simplicial_object C) ⥤_ ) ◫ NΓ.inv) ≫ (ΓN_trans ◫ 𝟙 N) : N ⟶ N) = 𝟙 N :=
begin
  ext P n,
  sorry
end

instance : is_iso (ΓN_trans : (N : karoubi (simplicial_object C) ⥤_ ) ⋙ _ ⟶ _) :=
begin
  haveI : ∀ (P : karoubi (simplicial_object C)), is_iso (ΓN_trans.app P), swap,
  { apply nat_iso.is_iso_of_is_iso_app, },
  intro P,
  haveI : is_iso (N.map (ΓN_trans.app P)), swap,
  { apply (N_reflects_iso C).reflects, },
  have h := congr_app identity_N P,
  simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app,
    (karoubi.functor_extension Γ ⋙ N).map_id, comp_id] at h,
  erw [id_comp, hom_comp_eq_id] at h,
  rw h,
  apply_instance,
end

def ΓN : N ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ≅ 𝟭 _ := as_iso (ΓN_trans)

@[simp]
lemma ΓN_hom : (ΓN.hom : (_ : karoubi (simplicial_object C) ⥤ _ ) ⟶ _ ) = ΓN_trans := as_iso_hom _

@[simps]
def NΓ_equivalence : karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ) :=
{ functor := N,
  inverse := karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ),
  unit_iso := ΓN.symm,
  counit_iso := NΓ,
  functor_unit_iso_comp' := λ P, begin
    have h := congr_app identity_N P,
    simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app,
      (karoubi.functor_extension Γ ⋙ N).map_id, comp_id] at h,
    erw [id_comp, ← ΓN_hom] at h,
    rw [← is_iso.inv_id],
    simp only [← h, is_iso.inv_comp],
    clear h,
    congr',
    { rw ← functor.map_inv,
      congr,
      rw ← comp_hom_eq_id,
      have h := congr_app ΓN.inv_hom_id P,
      simpa only [nat_trans.comp_app] using h, },
    { rw ← comp_hom_eq_id,
      have h := congr_app NΓ.hom_inv_id (N.obj P),
      simpa only [nat_trans.comp_app] using h, },
  end }

end dold_kan

end algebraic_topology
