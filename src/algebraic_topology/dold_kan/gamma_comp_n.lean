/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.functor_n
import algebraic_topology.dold_kan.degeneracies

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

--@[simps]
theorem NΓ : Γ ⋙ N ≅ 𝟭 (karoubi (chain_complex C ℕ)) := sorry
--(to_karoubi_iso_equiv _ _).inv_fun (NΓ'.trans (eq_to_iso (functor.comp_id _).symm))


#lint

end dold_kan

end algebraic_topology

