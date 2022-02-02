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

lemma P_infty_eq_zero_on (X : simplicial_object C) {n : ℕ} {Δ' : simplex_category.{v}} (i : Δ' ⟶ [n]) [mono i] 
  (h₁ : Δ'.len ≠ n) (h₂ : ¬is_d0 i) :
  P_infty.f n ≫ X.map i.op = 0 :=
begin
  have h₃ := simplex_category.len_le_of_mono (show mono i, by apply_instance),
  simp only [simplex_category.len_mk] at h₃,
  cases le_iff_exists_add.mp h₃ with c hc,
  by_cases hc' : c=1,
  { rw hc' at hc,
    unfreezingI { subst hc, },
    have fac := simplex_category.factorisation_non_surjective i _, swap,
    { by_contradiction h₄,
      simpa only [nat.one_ne_zero, add_le_iff_nonpos_right, simplex_category.len_mk, nonpos_iff_eq_zero]
        using simplex_category.len_le_of_epi (simplex_category.epi_iff_surjective.mpr h₄), },
    rcases fac with ⟨j,θ',hi⟩,
    have hj : j ≠ 0,
    { intro hj,
      unfold is_d0 at h₂,
      simp only [true_and, not_not, simplex_category.len_mk, eq_self_iff_true, hi, hj,
        simplex_category.hom.comp, simplex_category.hom.to_order_hom_mk, simplex_category.small_category_comp,
        function.comp_app, order_hom.comp_coe] at h₂,
      haveI : mono θ' := mono_of_mono_fac hi.symm,
      have h₄ := simplex_category.eq_eq_to_hom_of_is_iso (is_iso.of_iso
        (simplex_category.iso_of_bijective (simplex_category.bijective_of_mono_and_eq θ'
        (by simp only [simplex_category.mk_len])))),
      simp only [simplex_category.iso_of_bijective_hom] at h₄,
      rw h₄ at h₂,
      simpa only [simplex_category.eq_to_hom_eq, fin.mk_zero, fin.val_zero',
        simplex_category.δ, fin.one_eq_zero_iff, simplex_category.hom.to_order_hom_mk,
        simplex_category.mk_hom, order_embedding.to_order_hom_coe,
        nat.succ_ne_zero, fin.zero_succ_above, fin.succ_zero_eq_one] using h₂, },
    rw ← fin.succ_pred j hj at hi,
    erw [hi, op_comp, X.map_comp, ← assoc, P_infty_termwise,
      (higher_faces_vanish_P (Δ'.len+1) Δ'.len).vanishing _ le_add_self, zero_comp], },
  { have hc'' : 2 ≤ c := nat.succ_le_iff.mpr ((ne.symm hc').le_iff_lt.mp
      (nat.one_le_iff_ne_zero.mpr (by { simpa only [hc, self_eq_add_right, ne.def] using h₁, }))),
    cases nat.le.dest hc'' with k hk,
    rw add_comm at hk,
    rw [← hk, ← add_assoc] at hc,
    unfreezingI { subst hc, },
    have fac := simplex_category.factorisation_non_surjective i _, swap,
    { by_contradiction h₄,
      have h₅ := simplex_category.len_le_of_epi (simplex_category.epi_iff_surjective.mpr h₄),
      simp only [simplex_category.len_mk, add_assoc] at h₅,
      nth_rewrite 1 ← add_zero Δ'.len at h₅,
      simpa only [add_le_iff_nonpos_right, add_zero, nat.succ_ne_zero, nonpos_iff_eq_zero] using h₅, },
    rcases fac with ⟨j,θ',hi⟩,
    by_cases hj : j = 0, swap,
    { rw ← fin.succ_pred j hj at hi,
      erw [hi, op_comp, X.map_comp, ← assoc, P_infty_termwise,
        (higher_faces_vanish_P (Δ'.len+k+2) (Δ'.len+k+1)).vanishing _ le_add_self, zero_comp], },
    { have fac' := simplex_category.factorisation_non_surjective θ' _, swap,
      { by_contradiction h₄,
        have h₅ := simplex_category.len_le_of_epi (simplex_category.epi_iff_surjective.mpr h₄),
        simp only [simplex_category.len_mk, add_assoc] at h₅,
        nth_rewrite 1 ← add_zero Δ'.len at h₅,
        simpa only [add_le_iff_nonpos_right, add_zero, nonpos_iff_eq_zero] using h₅, },
      rcases fac' with ⟨j',θ'',hi'⟩,
      erw [hi', hj, assoc, ← simplex_category.δ_comp_δ (fin.zero_le j'), ← assoc] at hi,
      erw [hi, op_comp, X.map_comp, ← assoc,
        (higher_faces_vanish_P (Δ'.len+k+2) (Δ'.len+k+1)).vanishing _ le_add_self, zero_comp], }, }  
end

lemma P_infty_eq_zero_on' (X : simplicial_object C) {n : ℕ} {Δ' : simplex_category.{v}} (f : op [n] ⟶ op Δ') [mono f.unop]
  (h₁ : Δ'.len ≠ n) (h₂ : ¬is_d0 f.unop) :
  P_infty.f n ≫ X.map f = 0 :=
P_infty_eq_zero_on X f.unop h₁ h₂

lemma is_d0_eq {Δ Δ' : simplex_category.{u}} {i : Δ ⟶ Δ'} [mono i] (hi : is_d0 i) (k : fin (Δ.len+1)) :
  simplex_category.hom.to_order_hom i k = ⟨(k : ℕ)+1, by { have h := fin.is_lt k, rw hi.left, exact nat.succ_lt_succ h, }⟩ :=
begin
  have eq : Δ' = [Δ.len+1],
  { ext,
    rw [simplex_category.len_mk, hi.left], },
  unfreezingI { subst eq, },
  have fact := simplex_category.factorisation_non_surjective' i 0 _, swap,
  { intro x,
    apply (fin.pos_iff_ne_zero _).mp,
    apply lt_of_lt_of_le ((fin.pos_iff_ne_zero _).mpr hi.right),
    exact (simplex_category.hom.to_order_hom i).monotone (fin.zero_le x), },
  cases fact with θ' h1,
  haveI := mono_of_mono_fac h1.symm,
  have h2 := simplex_category.eq_eq_to_hom_of_is_iso (is_iso.of_iso
    (simplex_category.iso_of_bijective (simplex_category.bijective_of_mono_and_eq θ'
    (by simp only [simplex_category.mk_len])))),
  simp only [simplex_category.iso_of_bijective_hom] at h2,
  rw h2 at h1,
  simp only [h1, simplex_category.hom.comp, simplex_category.hom.to_order_hom_mk,
    simplex_category.small_category_comp, function.comp_app, order_hom.comp_coe,
    simplex_category.eq_to_hom_eq, simplex_category.δ],
  erw [fin.succ_above_zero, fin.ext_iff],
  simp only [fin.val_eq_coe, fin.coe_succ, fin.coe_mk],
end

lemma Γ_on_mono_comp_P_infty (X : simplicial_object C) {Δ Δ' : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i] :
  Γ_on_mono (alternating_face_map_complex.obj X) i ≫ P_infty.f (Δ'.len) = P_infty.f (Δ.len) ≫
    X.map (eq_to_hom (by simp only [simplex_category.mk_len]) ≫ i.op ≫ eq_to_hom (by simp only [simplex_category.mk_len])) :=
begin
  by_cases Δ = Δ',
  { unfreezingI { subst h, },
    simp only [Γ_on_mono_on_id, eq_to_hom_refl, id_comp],
    nth_rewrite 0 ← comp_id (P_infty.f Δ.len),
    erw ← X.map_id,
    congr',
    have h := is_iso.of_iso (simplex_category.iso_of_bijective (simplex_category.bijective_of_mono_and_eq i rfl)),
    simp only [simplex_category.iso_of_bijective_hom] at h,
    rw simplex_category.eq_eq_to_hom_of_is_iso h,
    simpa only [eq_to_hom_op, eq_to_hom_trans], },
  by_cases hi : is_d0 i,
  { erw [Γ_on_mono_on_d0 _ i hi, ← P_infty.comm' Δ.len Δ'.len hi.left.symm],
    dsimp [alternating_face_map_complex.obj, chain_complex.of],
    split_ifs with h', swap,
    { exfalso, exact h' hi.left, },
    simp only [preadditive.comp_sum],
    rw finset.sum_eq_single (0 : fin (Δ'.len+2)), rotate,
    { intros b hb hb',
      simp only [preadditive.comp_zsmul],
      erw ← eq_to_hom_map X, swap,
      { rw h', },
      erw ← X.map_comp,
      rw [P_infty_eq_zero_on', zsmul_zero],
      { rw h',
        simp only [nat.one_ne_zero, simplex_category.mk_len, self_eq_add_right, ne.def, not_false_iff], },
      { by_contradiction,
        have h' := h.right,
        simp only [simplex_category.hom.comp, quiver.hom.unop_op, simplex_category.hom.to_order_hom_mk,
          simplex_category.small_category_comp, function.comp_app, order_hom.comp_coe, eq_to_hom_unop, unop_comp,
          simplex_category.eq_to_hom_eq, fin.ext_iff, fin.coe_zero, fin.val_eq_coe, fin.coe_mk, fin.ne_iff_vne, ne.def,
          simplex_category.δ, simplex_category.mk_hom] at h',
        erw [(fin.succ_above_eq_zero_iff hb').mpr rfl, fin.coe_zero] at h',
        exact h' rfl, }, },
    { intro h,
      exfalso,
      simpa only [finset.mem_univ, not_true] using h, },
    simp only [fin.coe_zero, one_zsmul, pow_zero],
    congr' 1,
    erw ← eq_to_hom_map X, swap,
    { rw h', },
    erw ← X.map_comp,
    congr' 1,
    apply quiver.hom.unop_inj,
    simp only [unop_comp, eq_to_hom_unop, quiver.hom.unop_op],
    ext1, ext1, ext1 k,
    simp only [simplex_category.hom.comp, simplex_category.hom.to_order_hom_mk, simplex_category.small_category_comp,
      function.comp_app, order_hom.comp_coe, simplex_category.eq_to_hom_eq],
    erw fin.succ_above_zero,
    simp only [fin.ext_iff, fin.val_eq_coe, fin.coe_mk, fin.coe_succ, fin.eta, is_d0_eq hi k], },
  { rw [Γ_on_mono_eq_zero _ i h hi, zero_comp],
    rw P_infty_eq_zero_on',
    { simp only [simplex_category.mk_len, ne.def],
      by_contradiction h',
      exact h (simplex_category.ext _ _ h'.symm), },
    { by_contradiction h',
      apply hi,
      split,
      { exact h'.left, },
      { simpa only [unop_comp, eq_to_hom_unop, quiver.hom.unop_op,
          simplex_category.hom.comp, simplex_category.hom.to_order_hom_mk, simplex_category.small_category_comp,
          function.comp_app, order_hom.comp_coe, simplex_category.eq_to_hom_eq, fin.mk_zero, fin.val_zero',
          fin.val_eq_coe, fin.eta] using h'.right, }
    }, }
end

@[simps]
def ΓN'_trans : N' ⋙ functor_extension (Γ : chain_complex C ℕ ⥤ _)
  ⟶ to_karoubi _ :=
{ app := λ X,
  { f :=
    { app := λ Δ, sigma.desc (λ A, 
        P_infty.f _ ≫ X.map (eq_to_hom (by { simp only [simplex_category.mk_len] }) ≫ A.2.1.op)),
      naturality' := λ Δ Δ' θ, begin
        ext A,
        slice_rhs 1 2 { erw colimit.ι_desc, },
        dsimp,
        let em := image.mono_factorisation (θ.unop ≫ A.2.1),
        haveI : epi em.e := simplex_category.epi_of_mono_factorisation _,
        slice_lhs 1 2 { erw [Γ_simplicial_on_summand _ A em.fac], },
        slice_lhs 2 3 { erw colimit.ι_desc, },
        dsimp,
        slice_lhs 1 2 { erw Γ_on_mono_comp_P_infty, },
        simp only [assoc, ← X.map_comp],
        congr' 2,
        simp only [id_comp, eq_to_hom_refl, eq_to_hom_trans_assoc],
        congr' 1,
        rw [← op_comp, em.fac, op_comp, quiver.hom.op_unop],
        refl,
      end },
    comm := begin
      ext Δ A,
      dsimp,
      simp only [colimit.ι_desc],
      dsimp,
      slice_rhs 1 2 { erw ι_colim_map, },
      simp only [discrete.nat_trans_app, cofan.mk_ι_app, colimit.ι_desc,
        eq_to_hom_map, assoc, comp_id, functor.map_comp],
      slice_rhs 1 2 { erw P_infty_termwise_is_a_projector, },
      simp only [assoc],
    end },
  naturality' := λ X Y f, begin
    ext Δ A,
    simp only [N'_functor.map_f, N'_map, Γ_map_app, nat_trans.naturality, functor.comp_map, discrete.nat_trans_app, cofan.mk_ι_app,
      colimit.ι_desc_assoc, Γ_map_2, chain_complex.of_hom_f, colimit.ι_desc, ι_colim_map_assoc, assoc,
      alternating_face_map_complex.obj_d, functor_extension_map_f, alternating_face_map_complex_map,
      alternating_face_map_complex.map, functor.map_comp, karoubi.comp, nat_trans.comp_app, subtype.val_eq_coe,
      to_karoubi_map_f],
    slice_lhs 2 3 { erw P_infty_termwise_naturality, },
    slice_lhs 1 2 { erw P_infty_termwise_is_a_projector, },
    slice_lhs 2 3 { erw ← f.naturality, },
    simpa only [← assoc],
  end }

@[simps]
def ΓN_trans : N ⋙ functor_extension (Γ : chain_complex C ℕ ⥤ _)
  ⟶ 𝟭 _ :=
((to_karoubi_hom_equiv
    (N ⋙ functor_extension (Γ : chain_complex C ℕ ⥤ _)) (𝟭 _)).inv_fun)
    ((eq_to_hom (by { rw ← to_karoubi_comp_functor_extension' N', refl, }))
    ≫ ΓN'_trans ≫ eq_to_hom (functor.comp_id _).symm)

lemma identity_N : ((𝟙 (N : karoubi (simplicial_object C) ⥤_ ) ◫ NΓ.inv) ≫ (ΓN_trans ◫ 𝟙 N) : N ⟶ N) = 𝟙 N :=
begin
  ext P n,
  simp only [NΓ_inv_app_f_f, Γ_map_app, functor.comp_map, homological_complex.comp_f,
    Γ_map_2, N_obj_p_f, nat_trans.hcomp_app, ΓN_trans_app_f_app, nat_trans.id_app,
    N_map_f_f, assoc, karoubi.id_eq, functor_extension_map_f, karoubi.comp,
    nat_trans.comp_app],
  have eq₁ : P_infty.f n ≫ P_infty.f n = P_infty.f n := P_infty_termwise_is_a_projector n,
  have eq₂ : P.p.app (op [n]) ≫ P.p.app _ = P.p.app _,
  { simpa only [nat_trans.comp_app] using congr_app P.idempotence (op [n]), },
  have eq₃ : P.p.app (op [n]) ≫ P_infty.f n = P_infty.f n ≫ P.p.app (op [n]) :=
    P_infty_termwise_naturality _ _,
  slice_lhs 2 3 { erw comp_id, },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw ι_colim_map, erw discrete.nat_trans_app, },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw ι_colim_map, erw discrete.nat_trans_app, },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw ι_colim_map, erw discrete.nat_trans_app, },
  dsimp,
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw P_infty_eq_id_on_Γ_summand, },
  slice_lhs 3 4 { erw ι_colim_map, erw discrete.nat_trans_app, },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw eq₂, },
  slice_lhs 3 4 { erw ι_colim_map, erw discrete.nat_trans_app, },
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw comp_id, },
  slice_lhs 5 6 { erw id_comp, },
  slice_lhs 3 4 { erw colimit.ι_desc, },
  dsimp,
  slice_lhs 2 3 { erw eq₃, },
  slice_lhs 1 2 { erw eq₁, },
  slice_lhs 2 3 { erw comp_id, },
  simp only [assoc],
  erw P.X.map_id,
  slice_lhs 3 4 { erw id_comp, },
  erw eq₂,
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
    (functor_extension Γ ⋙ N).map_id, comp_id] at h,
  erw [id_comp, hom_comp_eq_id] at h,
  rw h,
  apply_instance,
end

def ΓN : N ⋙ functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ≅ 𝟭 _ := as_iso (ΓN_trans)

@[simp]
lemma ΓN_hom : (ΓN.hom : (_ : karoubi (simplicial_object C) ⥤ _ ) ⟶ _ ) = ΓN_trans := as_iso_hom _

@[simps]
def NΓ_equivalence : karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ) :=
{ functor := N,
  inverse := functor_extension (Γ : chain_complex C ℕ ⥤ _ ),
  unit_iso := ΓN.symm,
  counit_iso := NΓ,
  functor_unit_iso_comp' := λ P, begin
    have h := congr_app identity_N P,
    simp only [nat_trans.comp_app, nat_trans.hcomp_app, nat_trans.id_app,
      (functor_extension Γ ⋙ N).map_id, comp_id] at h,
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
