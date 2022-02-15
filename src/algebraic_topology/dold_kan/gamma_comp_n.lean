/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functor_n
import algebraic_topology.dold_kan.degeneracies
import for_mathlib.idempotents.nat_trans

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open category_theory.idempotents
--open opposite
open_locale simplicial

universe v

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category.{v} C] [additive_category C]

/-@[simps]
abbreviation NΓ'_hom : to_karoubi (chain_complex C ℕ) ⋙ Γ ⋙ N ⟶ to_karoubi _ :=
{ app := λ K,
  { f :=
    { f:= λ n, sigma.desc (λ A, begin
        by_cases A.1.len = n,
        { apply eq_to_hom,
          simp only [to_karoubi_obj_X],
          unfold Γ_summand,
          rw h, },
        { exact 0, }
      end),
      comm' := sorry, },
    comm := sorry, }, 
  naturality' := sorry, }

@[simps]
abbreviation NΓ'_inv :  to_karoubi (chain_complex C ℕ) ⟶ to_karoubi _ ⋙ Γ ⋙ N :=
{ app := λ K,
  { f :=
    { f := λ n, sigma.ι (Γ_summand K [n]) (Γ_index_id n),
      comm' := sorry, },
    comm := sorry, },
  naturality' := sorry, }

@[simps]
def NΓ' : to_karoubi (chain_complex C ℕ) ⋙ Γ ⋙ N ≅ to_karoubi _ :=
{ hom := NΓ'_hom,
  inv := NΓ'_inv,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

@[simps]
def NΓ : Γ ⋙ N ≅ 𝟭 (karoubi (chain_complex C ℕ)) :=
(whiskering_left_to_karoubi_iso_equiv (Γ ⋙ N) (𝟭 (karoubi (chain_complex C ℕ)))).inv_fun NΓ'
-/

--@[simps]
abbreviation NΓ'_hom : Γ' ⋙ N' ⟶ to_karoubi (chain_complex C ℕ) :=
{ app := λ K,
  { f :=
    { f:= λ n, sigma.desc (λ A, begin
        by_cases A.1.len = n,
        { apply eq_to_hom,
          simp only [to_karoubi_obj_X],
          unfold Γ_summand,
          rw h, },
        { exact 0, }
      end),
      comm' := sorry, },
    comm := sorry, }, 
  naturality' := sorry, }

--@[simps]
abbreviation NΓ'_inv : to_karoubi (chain_complex C ℕ) ⟶ Γ' ⋙ N' :=
{ app := λ K,
  { f :=
    { f := λ n, sigma.ι (Γ_summand K [n]) (Γ_index_id n),
      comm' := sorry, },
    comm := sorry, },
  naturality' := sorry, }

@[simps]
def NΓ' : Γ' ⋙ N' ≅ to_karoubi (chain_complex C ℕ) :=
{ hom := NΓ'_hom,
  inv := NΓ'_inv,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry, }

variable (C)

def to_karoubi_comp_Γ_comp_N : to_karoubi (chain_complex C ℕ) ⋙ Γ ⋙ N = Γ' ⋙ N' :=
begin
  have h := congr_obj (functor_extension''_comp_whiskering_left_to_karoubi (chain_complex C ℕ) (simplicial_object C)) Γ',
  have h' := congr_obj (functor_extension'_comp_whiskering_left_to_karoubi (simplicial_object C) (chain_complex C ℕ)) N',
  dsimp at h h',
  erw [← functor.assoc, h, functor.assoc, h'],
end

variable {C}
/-
@[simps]
def NΓ'' : to_karoubi (chain_complex C ℕ) ⋙ Γ ⋙ N ≅ to_karoubi _ :=
(eq_to_iso (to_karoubi_comp_Γ_comp_N C)).trans NΓ'-/

@[simps]
def NΓ : Γ ⋙ N ≅ 𝟭 (karoubi (chain_complex C ℕ)) :=
(whiskering_left_to_karoubi_iso_equiv (Γ ⋙ N) (𝟭 (karoubi (chain_complex C ℕ)))).inv_fun
((eq_to_iso (to_karoubi_comp_Γ_comp_N C)).trans NΓ')

--(whiskering_left_to_karoubi_iso_equiv (Γ ⋙ N) (𝟭 (karoubi (chain_complex C ℕ)))).inv_fun NΓ'

end dold_kan

end algebraic_topology

