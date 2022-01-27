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

variables {C : Type*} [category.{v} C] [additive_category C]

lemma is_d0_iff {j : ℕ} {i : fin (j+2)} : is_d0 (simplex_category.δ i) ↔ i = 0 :=
begin
  split,
  { rintro ⟨h₁,h₂⟩,
    by_contradiction,
    erw fin.succ_above_ne_zero_zero h at h₂,
    exact h₂ rfl, },
  { intro h,
    subst h,
    split,
    { refl, },
    { erw fin.succ_above_zero,
      simp only [fin.one_eq_zero_iff, nat.succ_ne_zero, fin.succ_zero_eq_one,
        ne.def, not_false_iff], }, }
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

lemma inclusion_Γ_summand_decomp (K : chain_complex C ℕ) {Δ Δ' : simplex_category.{v}} (e : Δ ⟶ Δ') [epi e] :
  sigma.ι (Γ_summand K Δ') ⟨Δ', ⟨𝟙 _, by apply_instance⟩⟩ ≫
  Γ_simplicial K e =
  sigma.ι (Γ_summand K Δ) ⟨Δ', ⟨e, by apply_instance⟩⟩ :=
begin
  erw Γ_simplicial_on_summand K ⟨Δ', ⟨𝟙 _, by apply_instance⟩⟩
    (show e ≫ 𝟙 _ = e ≫ 𝟙 _, by refl),
  erw [Γ_on_mono_on_id K (𝟙 Δ') rfl, eq_to_hom_refl, id_comp],
end

lemma factorisation_non_injective {n : ℕ} {Δ' : simplex_category} (θ : [n+1] ⟶ Δ')
  (hθ : ¬function.injective θ.to_order_hom) :
  ∃ (i : fin(n+1)) (θ' : [n] ⟶ Δ'), θ = simplex_category.σ i ≫ θ' :=
begin
  simp only [function.injective, exists_prop, not_forall] at hθ,
  have hθ₂ : ∃ (x y : fin (n+2)), (simplex_category.hom.to_order_hom θ) x =
    (simplex_category.hom.to_order_hom θ) y ∧ x<y,
  { rcases hθ with ⟨x,y,⟨h₁,h₂⟩⟩,
    by_cases x<y,
    { exact ⟨x, y, ⟨h₁, h⟩⟩, },
    { refine ⟨y, x, ⟨h₁.symm, _⟩⟩,
      cases lt_or_eq_of_le (not_lt.mp h) with h' h',
      { exact h', },
      { exfalso,
        exact h₂ h'.symm, }, }, },
  rcases hθ₂ with ⟨x,y,⟨h₁,h₂⟩⟩,
  have hx : (x : ℕ) < n+1 := lt_of_lt_of_le (fin.lt_iff_coe_lt_coe.mp h₂) (nat.lt_succ_iff.mp (fin.is_lt y)),
  let x' : fin(n+1) := ⟨x.val, hx⟩,
  use x',
  let f' : fin(n+1) → fin(Δ'.len+1) := λ j, if (j : ℕ) ≤ x.val
    then θ.to_order_hom j.cast_succ
    else θ.to_order_hom j.succ,
  let F : fin([n].len+1) →o fin(Δ'.len+1) := ⟨f', _⟩, swap,
  { intros a b hab,
    dsimp [f'],
    split_ifs with ha hb; apply θ.to_order_hom.monotone',
    { simpa only, },
    { simp only [not_le] at hb,
      rw fin.le_iff_coe_le_coe,
      simp only [fin.coe_succ, fin.coe_cast_succ],
      exact le_add_right (fin.le_iff_coe_le_coe.mp hab), },
    { exfalso,
      exact ha (le_trans (fin.le_iff_coe_le_coe.mp hab) h), },
    { simpa only [fin.succ_le_succ_iff], }, },
  use simplex_category.hom.mk F,
  ext1, ext1, ext1 j,
  simp only [simplex_category.hom.comp, simplex_category.hom.to_order_hom_mk,
    simplex_category.small_category_comp, function.comp_app, order_hom.comp_coe,
    order_hom.coe_fun_mk, coe_coe],
  simp [simplex_category.σ, f'],
  by_cases hj : j ≤ fin.cast_succ x',
  { rw fin.pred_above_below x' j hj,
    have hj' : j < fin.last (n+1),
    { simp only [fin.lt_iff_coe_lt_coe, fin.coe_last],
      rw fin.le_iff_coe_le_coe at hj,
      simp only [fin.val_eq_coe, fin.cast_succ_mk, fin.eta] at hj,
      exact lt_of_le_of_lt hj hx, },
    split_ifs,
    { congr,
      rw fin.cast_succ_cast_pred,
      exact hj', },
    { exfalso,
      apply h,
      simpa only [fin.lt_last_iff_coe_cast_pred.mp hj', fin.val_eq_coe,
        fin.le_iff_coe_le_coe, fin.cast_succ_mk, fin.eta] using hj, }, },
  { simp only [not_le] at hj,
    simp only [fin.pred_above_above x' j hj],
    split_ifs,
    { rw fin.lt_iff_coe_lt_coe at hj,
      cases le_iff_exists_add.mp (nat.succ_le_iff.mpr hj) with c hc,
      simp only [fin.val_eq_coe, fin.cast_succ_mk, fin.eta] at hc,
      rw [fin.coe_pred, hc] at h,
      simp only [add_le_iff_nonpos_right, nat.succ_add_sub_one, nonpos_iff_eq_zero] at h,
      rw [h, add_zero] at hc,
      have eq : (simplex_category.hom.to_order_hom θ) x = (simplex_category.hom.to_order_hom θ) j,
      { rw le_antisymm_iff,
        split,
        { apply θ.to_order_hom.monotone',
          rw [fin.le_iff_coe_le_coe, hc],
          exact nat.le_succ _, },
        { rw h₁,
          apply θ.to_order_hom.monotone',
          rw [fin.le_iff_coe_le_coe, hc],
          rw [fin.lt_iff_coe_lt_coe] at h₂,
          exact nat.succ_le_iff.mpr h₂, }, },
      rw ← eq,
      congr,
      ext,
      simp only [fin.coe_cast_succ, fin.coe_pred, hc,
        tsub_zero, nat.succ_sub_succ_eq_sub], },
    { simp only [fin.succ_pred], }, },
end

lemma P_infty_eq_zero_on_σ (X : simplicial_object C)
  {n : ℕ} (i : fin (n+1)) :
  (X.σ i) ≫ P_infty.f (n+1) = 0 :=
begin
  sorry
end

lemma P_infty_eq_zero_on_degeneracies (X : simplicial_object C)
  {n : ℕ} {Δ' : simplex_category} (θ : [n] ⟶ Δ')
  (hf : ¬function.injective θ.to_order_hom) :
  X.map θ.op ≫ P_infty.f n = 0 :=
begin
  cases n,
  { exfalso,
    simp only [function.injective, exists_prop, not_forall] at hf,
    rcases hf with ⟨x,y,⟨h₁,h₂⟩⟩,
    have hx := fin.is_lt x,
    have hy := fin.is_lt y,
    simp only [simplex_category.len_mk, nat.lt_one_iff] at hx hy,
    simp only [fin.ext_iff, hx, hy] at h₂,
    exact h₂ rfl, },
  { rcases factorisation_non_injective θ hf with ⟨i,θ,h⟩,
    erw [h, op_comp, X.map_comp, assoc,
      P_infty_eq_zero_on_σ X i, comp_zero], }
end

#exit

lemma P_infty_eq_zero_on_Γ_summand (K : chain_complex C ℕ) {n : ℕ} {A : Γ_index_set [n]} (hA : ¬A.1.len = n) :
  inclusion_Γ_summand K A ≫ P_infty.f n = 0 :=
begin
  have h : ¬function.injective A.2.1.to_order_hom,
  { by_contradiction,
    apply hA,
    simpa only [fintype.card_fin, add_left_inj] using
      (fintype.card_of_bijective ⟨h, simplex_category.epi_iff_surjective.mp A.snd.property⟩).symm, },
  haveI : epi A.2.1 := A.2.2,
  rw [show A = ⟨A.1,⟨A.2.1,A.2.2⟩⟩, by { ext, { simp only, }, { apply heq_of_eq, ext1, refl, } }],
  slice_lhs 1 1 { dsimp, erw ← inclusion_Γ_summand_decomp K A.2.1, },  
  rw [assoc, show Γ_simplicial K A.2.1 = (Γ.obj K).map A.2.1.op, by refl],
  slice_lhs 2 3 { erw P_infty_eq_zero_on_degeneracies _ A.2.1 h, },
  erw comp_zero,
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
              simp only [preadditive.comp_zsmul],
              erw Γ_simplicial_on_summand K (Γ_index_id (j+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
              rw Γ_on_mono_eq_zero, rotate,
              { intro h,
                simpa only [simplex_category.len_mk, nat.succ_ne_self, Γ_index_id_fst]
                  using congr_arg simplex_category.len h, },
              { rw is_d0_iff,
                exact hk, },
              simp only [smul_zero', zero_comp], },
            { intro h,
              exfalso,
              simpa only [finset.mem_univ, not_true] using h, },
            simp only [fin.coe_zero, one_zsmul, pow_zero],
            let i := simplex_category.δ (0 : fin (j+2)),
            erw Γ_simplicial_on_summand K (Γ_index_id (j+1)) (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
            congr,
            exact Γ_on_mono_on_d0 K i (is_d0_iff.mpr rfl), },
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

end dold_kan

end algebraic_topology
