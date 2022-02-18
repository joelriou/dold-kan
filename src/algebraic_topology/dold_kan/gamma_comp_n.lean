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

@[simp]
def NΓ'_map_termwise (K : chain_complex C ℕ) (n : ℕ) (A : Γ_index_set [n]) :
Γ_summand K [n] A ⟶ ((to_karoubi (chain_complex C ℕ)).obj K).X.X n :=
begin
  by_cases A.1.len = n,
  { apply eq_to_hom,
    simp only [to_karoubi_obj_X],
    unfold Γ_summand,
    rw h, },
  { exact 0, }
end

lemma d_on_KΓ (K : chain_complex C ℕ) (j : ℕ) :
  inclusion_Γ_summand K (Γ_index_id (j+1)) ≫ K[Γ'.obj K].d (j+1) j
    ≫ sigma.desc (NΓ'_map_termwise K j) = K.d (j+1) j :=
begin
  erw chain_complex.of_d,
  dsimp,
  simp only [preadditive.sum_comp, preadditive.comp_sum, preadditive.zsmul_comp, preadditive.comp_zsmul, ← assoc],
  erw finset.sum_eq_single (0 : fin (j+2)), rotate,
  { intros b hb₀ hb,
    let i := simplex_category.δ b,
    erw Γ_simplicial_on_summand K (Γ_index_id (j+1))
      (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
    erw Γ_on_mono_eq_zero K i (λ hj, by simpa only [simplex_category.len_mk, nat.succ_ne_self]
      using congr_arg simplex_category.len hj) (by { rw is_d0_iff, exact hb, }),
    simp only [smul_zero', zero_comp], },
  { intro h, exfalso, simpa only [finset.mem_univ, not_true] using h, },
  { simp only [fin.coe_zero, pow_zero, ← assoc, one_zsmul],
    let i := simplex_category.δ (0 : fin (j+2)),
    erw Γ_simplicial_on_summand K (Γ_index_id (j+1))
      (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
    erw [Γ_on_mono_on_d0 K i (is_d0_iff.mpr rfl), assoc],
    simp only [NΓ'_map_termwise, colimit.ι_desc, cofan.mk_ι_app, simplex_category.len_mk,
      eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true],
    erw comp_id,
    refl, },
end

lemma d_on_KΓ' (K : chain_complex C ℕ) (j : ℕ) (A : Γ_index_set [j+1]) (hA : ¬A.fst.len = j+1) :
inclusion_Γ_summand K A ≫ K[Γ'.obj K].d (j + 1) j ≫ sigma.desc (NΓ'_map_termwise K j) = 0 :=
begin
  erw chain_complex.of_d,
  dsimp,
  simp only [preadditive.sum_comp, preadditive.comp_sum, preadditive.zsmul_comp, preadditive.comp_zsmul, ← assoc],
  by_cases hA' : A.1.len = j, swap,
  { apply finset.sum_eq_zero,
    intros i hi,
    let em := image.mono_factorisation (simplex_category.δ i ≫ A.2.1),
    haveI : epi em.e := simplex_category.epi_of_mono_factorisation _,
    erw [Γ_simplicial_on_summand K A em.fac, assoc, colimit.ι_desc, cofan.mk_ι_app,
      NΓ'_map_termwise],
    split_ifs, swap,
    { erw [comp_zero, smul_zero'], },
    { exfalso,
      simp only at h,
      have hi' := simplex_category.len_le_of_mono em.m_mono,
      rw h at hi',
      cases nat.le.dest hi' with b hb,
      have he := simplex_category.len_le_of_epi A.2.2,
      simp only [simplex_category.len_mk] at he,
      simp only [← hb, add_right_inj, add_le_add_iff_left] at hA he,
      have hb' := nat.lt_one_iff.mp ((ne.le_iff_lt hA).mp he),
      rw [← hb, hb'] at hA',
      exact hA' rfl, }, },
  { sorry, },
end

@[simps]
abbreviation NΓ'_hom : Γ' ⋙ N' ⟶ to_karoubi (chain_complex C ℕ) :=
{ app := λ K,
  { f :=
    { f:= λ n, sigma.desc (NΓ'_map_termwise K n),
      comm' := λ i j hij, begin
        have h : j+1 = i := hij,
        subst h,
        ext A,
        simp only [cofan.mk_ι_app, colimit.ι_desc_assoc, NΓ'_map_termwise],
        split_ifs,
        { have hA := eq_Γ_index_id h,
          subst hA,
          dsimp,
          erw [id_comp, d_on_KΓ], },
        { rw zero_comp,
          dsimp,
          exact (d_on_KΓ' K j A h).symm, },
      end },
    comm := begin
      ext n A,
      simp only [to_karoubi_obj_p, homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc],
      dsimp,
      erw [comp_id],
      split_ifs,
      { have hA := eq_Γ_index_id h,
        subst hA,
        slice_rhs 1 2 { erw P_infty_eq_id_on_Γ_summand, },
        simp only [NΓ'_map_termwise, inclusion_Γ_summand, eq_to_hom_refl, colimit.ι_desc, cofan.mk_ι_app,
          Γ_index_id_fst, simplex_category.len_mk, eq_self_iff_true, dite_eq_ite, if_true], },
      { erw [← assoc, P_infty_eq_zero_on_Γ_summand K h, zero_comp], },
    end }, 
  naturality' := λ K L f, begin
    ext n A,
    simp,
    erw [← assoc],
    split_ifs,
    { have hA := eq_Γ_index_id h,
      subst hA,
      erw P_infty_eq_id_on_Γ_summand,
      simp only [NΓ'_map_termwise, inclusion_Γ_summand, ι_colim_map_assoc, discrete.nat_trans_app, colimit.ι_desc,
        cofan.mk_ι_app, Γ_index_id_fst, simplex_category.len_mk, eq_self_iff_true, eq_to_hom_refl,
        dite_eq_ite, if_true],
      erw [id_comp, comp_id],
      refl, },
    { erw [P_infty_eq_zero_on_Γ_summand K h, zero_comp, zero_comp], },
  end, }

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
    simpa only [NΓ'_map_termwise, homological_complex.comp_f, cofan.mk_ι_app, karoubi.comp,
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

