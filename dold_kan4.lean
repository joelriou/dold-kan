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

lemma d0_is_d0 {j : ℕ} (i : [j] ⟶ [j+1]) [mono i] (hi : i = simplex_category.δ (0 : fin(j+2))) : is_d0 i :=
begin
  unfreezingI { subst hi, },
  split,
  { refl, },
  { erw fin.succ_above_zero,
    simp only [fin.one_eq_zero_iff, nat.succ_ne_zero, fin.succ_zero_eq_one,
      ne.def, not_false_iff], }
end

lemma neg_is_d0 {j : ℕ} {k : fin(j+2)} (i : [j] ⟶ [j+1]) [mono i]
  (hi : i = simplex_category.δ k) (hk : k ≠ 0): ¬is_d0 i :=
begin
  unfreezingI { subst hi, },
  rintro ⟨h₁,h₂⟩,
  erw fin.succ_above_ne_zero_zero hk at h₂,
  exact h₂ rfl,
end

lemma mono_δ {n : ℕ} {i : fin(n+2)} : mono (simplex_category.δ i) :=
begin
  rw simplex_category.mono_iff_injective,
  exact fin.succ_above_right_injective,
end

@[simp]
def inclusion_Γ_summand (K : chain_complex C ℕ) {n : ℕ} (A : Γ_index_set [n]) :
  Γ_summand K (unop (op [n])) A ⟶ ((alternating_face_map_complex C).obj (Γ.obj K)).X n := sigma.ι (Γ_summand K [n]) A

@[simps]
def Γ_index_id (n : ℕ) : Γ_index_set [n] := ⟨[n], ⟨𝟙 _, by apply_instance,⟩⟩

lemma P_infty_eq_id_on_Γ_summand (K : chain_complex C ℕ) (n : ℕ) :
  inclusion_Γ_summand K (Γ_index_id n) ≫ P_infty.f n = inclusion_Γ_summand K (Γ_index_id n) := 
begin
  rw P_infty_termwise,
  cases n,
  { rw [P_deg0_eq, comp_id], },
  { apply P_is_identity_where_faces_vanish,
    { refine ⟨_⟩,
      intros j hj,
      let i := simplex_category.δ j.succ,
      haveI : mono i := mono_δ,
      erw Γ_simplicial_on_summand K (Γ_index_id (n+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
      rw [Γ_on_mono_eq_zero K i _ _, zero_comp],
      { intro h,
        apply nat.succ_ne_self n,
        have h' := congr_arg simplex_category.len h,
        simpa only [simplex_category.len_mk] using congr_arg simplex_category.len h, },
      { rintro ⟨h₁,h₂⟩,
        erw fin.succ_above_below j.succ 0 (fin.succ_pos j) at h₂,
        simpa only [fin.cast_succ_zero, eq_self_iff_true, not_true, ne.def] using h₂, }, }, }
end

lemma P_infty_eq_zero_on_Γ_summand (K : chain_complex C ℕ) {n : ℕ} {A : Γ_index_set [n]} (hA : ¬A.1.len = n) :
  inclusion_Γ_summand K A ≫ P_infty.f n = 0 :=
begin
  sorry
end

lemma A_eq {n : ℕ} {A : Γ_index_set [n]} (h : A.1.len = n) : A = Γ_index_id n :=
begin
  rcases A with ⟨Δ,⟨f,hf⟩⟩,
  have hΔ : Δ = [n],
  { apply simplex_category.ext,
    rw [h, simplex_category.len_mk], },
  subst hΔ,
  simp only [Γ_index_id],
  ext,
  { refl, },
  { apply heq_of_eq,
    haveI := hf,
    simpa only [simplex_category.is_iso_of_bijective_hom] using congr_arg (λ (φ : _ ≅ _), φ.hom)
      (simplex_category.iso_refl_of_iso
      (simplex_category.is_iso_of_bijective (simplex_category.bijective_of_epi_and_eq f rfl))), }
end

abbreviation NΓ'_hom : to_karoubi _ ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N
  ⟶ to_karoubi _ :=
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
          { dsimp,
            split_ifs with h',
            { sorry, },
            { exfalso,
              exact h' hij.symm, }, },
          { rw [zero_comp],
            dsimp,
            split_ifs with h',
            { subst h',
              simp only [id_comp, eq_to_hom_refl, ← assoc],
              erw preadditive.comp_sum,
              sorry, },
            { exfalso,
              exact h' hij.symm, }, },
        end, },
      comm := begin
        ext n A,
        simp only [to_karoubi_obj_p, homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc],
        dsimp,
        erw [comp_id],
        split_ifs,
        { have h' := A_eq h,
          subst h',
          slice_rhs 1 2 { erw P_infty_eq_id_on_Γ_summand, },
          simp only [Γ_index_id_fst, dite_eq_ite, discrete.nat_trans_app, if_true,
            cofan.mk_ι_app, simplex_category.len_mk, eq_self_iff_true, ι_colim_map,
            colimit.ι_desc, assoc, eq_to_hom_refl, inclusion_Γ_summand],
          erw [id_comp], },
        { slice_rhs 1 2 { erw P_infty_eq_zero_on_Γ_summand K h, },
          simp only [zero_comp], }
      end },
    naturality' := λ K L f, begin
      ext n A,
      simp only [Γ_map_app, functor.comp_map, homological_complex.comp_f,
        cofan.mk_ι_app, colimit.ι_desc_assoc, Γ_map_2, N_map_f_f, dif_neg,
        assoc, karoubi.functor_extension_map_f, karoubi.comp, to_karoubi_map_f],
      split_ifs,
      { have h' := A_eq h,
        subst h',
        slice_lhs 1 2 { erw P_infty_eq_id_on_Γ_summand, },
        simp only [Γ_index_id_fst, dite_eq_ite, discrete.nat_trans_app, if_true,
          cofan.mk_ι_app, simplex_category.len_mk, eq_self_iff_true, ι_colim_map,
          colimit.ι_desc, assoc, eq_to_hom_refl, inclusion_Γ_summand],
        erw [comp_id, id_comp],
        refl, },
      { slice_lhs 1 2 { erw P_infty_eq_zero_on_Γ_summand K h, },
        simp only [zero_comp], }
    end }

abbreviation NΓ'_inv :  to_karoubi _ ⟶ to_karoubi _ ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N
 :=
  { app := λ K,
    { f :=
      { f := λ n, sigma.ι (Γ_summand K [n]) (Γ_index_id n),
        comm' := λ i j hij, begin
          dsimp,
          split_ifs,
          { subst h,
            simp only [id_comp, eq_to_hom_refl, preadditive.comp_sum],
            erw finset.sum_eq_single (0 : fin (j+2)), rotate,
            { intros k h hk,
              let i := simplex_category.δ k,
              haveI : mono i := mono_δ,
              simp only [preadditive.comp_zsmul],
              erw Γ_simplicial_on_summand K (Γ_index_id (j+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
              rw Γ_on_mono_eq_zero, rotate,
              { intro h,
                simpa only [simplex_category.len_mk, nat.succ_ne_self, Γ_index_id_fst]
                  using congr_arg simplex_category.len h, },
              { exact neg_is_d0 i rfl hk, },
              simp only [smul_zero', zero_comp], },
            { intro h,
              exfalso,
              simpa only [finset.mem_univ, not_true] using h, },
            simp only [fin.coe_zero, one_zsmul, pow_zero],
            let i := simplex_category.δ (0 : fin (j+2)),
            haveI : mono i := mono_δ,
            erw Γ_simplicial_on_summand K (Γ_index_id (j+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
            congr,
            exact Γ_on_mono_on_d0 K i (d0_is_d0 i rfl), },
          { exfalso,
            exact h hij.symm, },
        end },
      comm := begin
        ext n,
        dsimp,
        slice_rhs 2 3 { erw P_infty_eq_id_on_Γ_summand, },
        simp only [discrete.nat_trans_app, ι_colim_map, inclusion_Γ_summand],
        erw [id_comp, id_comp],
      end },
    naturality' := λ K L f, begin
      ext n,
      simp only [Γ_map_app, functor.comp_map, homological_complex.comp_f, Γ_map_2,
        N_map_f_f, karoubi.functor_extension_map_f, karoubi.comp, to_karoubi_map_f],
      erw [← assoc, P_infty_eq_id_on_Γ_summand],
      simpa only [discrete.nat_trans_app, ι_colim_map, inclusion_Γ_summand],
    end }

lemma NΓ' : to_karoubi _ ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N
  ≅ to_karoubi _ :=
{ hom := NΓ'_hom,
  inv := NΓ'_inv,
  hom_inv_id' := begin
    ext K n A,
    simp only [homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc_assoc,
      nat_trans.id_app, karoubi.id_eq, karoubi.comp, nat_trans.comp_app],
    dsimp,
    split_ifs,
    { have h' := A_eq h,
      subst h',
      erw [← assoc, P_infty_eq_id_on_Γ_summand],
      simpa only [discrete.nat_trans_app, ι_colim_map, inclusion_Γ_summand,
        eq_to_hom_refl], },
    { erw [zero_comp, ← assoc, P_infty_eq_zero_on_Γ_summand K h, zero_comp], },
  end,
  inv_hom_id' := begin
    ext K n,
    dsimp,
    simpa only [homological_complex.comp_f, cofan.mk_ι_app, karoubi.comp,
      simplex_category.len_mk, eq_self_iff_true, colimit.ι_desc, Γ_index_id],
  end }

@[simps]
theorem NΓ : karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N ≅ 𝟭 _ :=
(karoubi.to_karoubi_iso_equiv _ _).inv_fun (NΓ'.trans (eq_to_iso (functor.comp_id _).symm))

#print NΓ

end dold_kan

end algebraic_topology
