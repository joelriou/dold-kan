import category_theory.additive.basic
import category_theory.limits.shapes.images
import data.sigma.basic
import data.fintype.basic
import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import simplex_category

import dold_kan2
import dold_kan3

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

variables {C : Type*} [category C] [additive_category C]

--lemma eq_of_eq_to_iso

theorem NΓ : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ to_karoubi _ ⋙ N
  ≅ to_karoubi _ :=
{ hom :=
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
      comm := sorry, }, },
  inv :=
  { app := λ K,
    { f :=
      { f := λ n, sigma.ι (Γ_summand K [n]) (⟨[n], ⟨𝟙 _, by apply_instance⟩⟩),
        comm' := sorry },
      comm := sorry}, },
  hom_inv_id' := begin
    ext K n A,
    simp only [homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc_assoc,
      nat_trans.id_app, karoubi.id_eq, karoubi.comp, nat_trans.comp_app],
    dsimp,
    split_ifs,
    { have h' : A = ⟨[n],⟨𝟙 _,by apply_instance⟩⟩ := sorry,
      subst h',
      sorry, },
    { erw [zero_comp, comp_id],
      sorry, },
  end,
  inv_hom_id' := begin
    ext K n,
    dsimp,
    simpa only [homological_complex.comp_f, cofan.mk_ι_app, karoubi.comp,
      simplex_category.len_mk, eq_self_iff_true, colimit.ι_desc],
  end }

#check N
#check Γ

end dold_kan

end algebraic_topology
