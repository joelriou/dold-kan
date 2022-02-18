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
      comm' := λ i j hij, begin
        ext A,
        simp only [cofan.mk_ι_app, colimit.ι_desc_assoc],
        split_ifs,
        sorry,
        sorry,
      end },
    comm := sorry, }, 
  naturality' := sorry, }

@[simps]
abbreviation NΓ'_inv : to_karoubi (chain_complex C ℕ) ⟶ Γ' ⋙ N' :=
{ app := λ K,
  { f :=
    { f := λ n, sigma.ι (Γ_summand K [n]) (Γ_index_id n),
      comm' := λ i j hij, begin
        have h : j+1 = i := hij,
        subst h,
        erw [chain_complex.of_d, preadditive.comp_sum],
        erw finset.sum_eq_single (0 : fin (j+2)), rotate,
        { intros b hb hb',
          let i := simplex_category.δ b,
          rw [preadditive.comp_zsmul],
          erw Γ_simplicial_on_summand K (Γ_index_id (j+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          rw [Γ_on_mono_eq_zero K i, zero_comp, zsmul_zero],
          { intro h,
            exact nat.succ_ne_self j (congr_arg simplex_category.len h), },
          { rw is_d0_iff, exact hb', }, },
        { simp only [finset.mem_univ, not_true, forall_false_left], },
        { simp only [fin.coe_zero, pow_zero, one_zsmul],
          let i := simplex_category.δ (0 : fin (j+2)),
          erw Γ_simplicial_on_summand K (Γ_index_id (j+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          congr',
          apply Γ_on_mono_on_d0 K i,
          erw is_d0_iff, },
      end },
    comm := begin
      ext n,
      dsimp,
      slice_rhs 2 3 { erw P_infty_eq_id_on_Γ_summand, },
      simp only [discrete.nat_trans_app, ι_colim_map, inclusion_Γ_summand, id_comp],
    end },
  naturality' := λ K L f, begin
    ext n,
    simp only [karoubi.comp, homological_complex.comp_f],
    erw [← assoc, P_infty_eq_id_on_Γ_summand, ι_colim_map, discrete.nat_trans_app],
    refl,
  end }

@[simps]
def NΓ' : Γ' ⋙ N' ≅ to_karoubi (chain_complex C ℕ) :=
{ hom := NΓ'_hom,
  inv := NΓ'_inv,
  hom_inv_id' := begin
    ext K n A,
    simp only [homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc_assoc,
      nat_trans.id_app, karoubi.id_eq, karoubi.comp, nat_trans.comp_app],
    dsimp,
    split_ifs,
    { have h' := eq_Γ_index_id h,
      subst h',
      erw [P_infty_eq_id_on_Γ_summand, id_comp],refl, },
    { erw [zero_comp, P_infty_eq_zero_on_Γ_summand K h], },
  end,
  inv_hom_id' := begin
    ext K n,
    dsimp,
    simpa only [homological_complex.comp_f, cofan.mk_ι_app, karoubi.comp,
      simplex_category.len_mk, eq_self_iff_true, colimit.ι_desc, Γ_index_id],
  end }


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

