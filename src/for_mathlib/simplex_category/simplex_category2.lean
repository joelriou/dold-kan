import algebraic_topology.simplex_category
import category_theory.limits.shapes.images

universes u v

open category_theory
open category_theory.limits

namespace simplex_category

def strong_epi_of_epi {X Y : simplex_category} (f : X ⟶ Y) [epi f] :
  strong_epi f :=
{ epi := by apply_instance,
  has_lift := λ A B u v w hw comm,
  begin
    have comm' := λ (x : fin (X.len+1)), congr_arg (λ F, hom.to_order_hom F x) comm,
    simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe,
      hom.comp, small_category_comp] at comm',
    have surjectivity := epi_iff_surjective.mp (infer_instance : epi f),
    let lift := function.inv_fun f.to_order_hom,
    have hlift : ∀ y, f.to_order_hom (lift y) = y := function.right_inverse_inv_fun surjectivity,
    let γ' := λ y, u.to_order_hom (lift y),
    have hγ' : ∀ x, γ' (f.to_order_hom x) = u.to_order_hom x,
    { intro x,
      apply mono_iff_injective.mp hw,
      simp only [comm', hlift], },
    let γ : Y ⟶ A := hom.mk
      { to_fun := γ',
        monotone' := λ y₁ y₂ h, begin
          cases eq_or_lt_of_le h with h' h',
          { rw h', },
          { apply (hom.to_order_hom u).monotone,
            by_contradiction h'',
            have ineq := (hom.to_order_hom f).monotone (le_of_lt (not_le.mp h'')),
            simp only [hlift, order_hom.to_fun_eq_coe] at ineq,
            rw [le_antisymm h ineq] at h',
            exact (irrefl y₂ : ¬(y₂<y₂)) h', },
        end, },
    exact ⟨nonempty.intro
    { lift := γ,
      fac_left' := by { ext1, ext1, ext1, exact hγ' x, },
      fac_right' := by { ext y, dsimp, rw [← hlift y, hγ', comm'], }, }⟩,
  end }

def strong_epi_mono_factorisation_of_epi_mono_factorisation
  {x y z : simplex_category} (f : x ⟶ z) (e : x ⟶ y) (i : y ⟶ z)
  [epi e] [mono i] (h : e ≫ i = f) : strong_epi_mono_factorisation f :=
begin
  haveI : strong_epi e := strong_epi_of_epi e,
  exact { I := y, m := i, e := e, m_mono := by apply_instance, fac' := h, },
end

instance : has_strong_epi_mono_factorisations simplex_category :=
begin
  constructor,
  intros x y f,
  let α := { j // ∃ i, f.to_order_hom i = j },
  let ψ : order_hom _ α :=
    ⟨λ i, ⟨f.to_order_hom i, ⟨i, rfl⟩⟩, λ _ _ h, f.to_order_hom.monotone h⟩,
  let n := fintype.card α-1,
  have eq : fintype.card α = n+1,
  { cases nat.eq_zero_or_eq_succ_pred (fintype.card α),
    { exfalso,
      rw fintype.card_eq_zero_iff at h,
      apply h.false,
      exact ⟨f.to_order_hom 0, ⟨0, rfl⟩⟩, },
    { exact h, }, },
  let φ := mono_equiv_of_fin α eq,
  let γ : order_hom α (fin (y.len+1)) := ⟨λ j, j.1, λ _ _ h, h, ⟩,
  let e : x ⟶ mk n := hom.mk (order_hom.comp
    (order_embedding.to_order_hom (order_iso.to_order_embedding φ.symm)) ψ),
  haveI : epi e,
  { apply epi_iff_surjective.mpr,
    intro k,
    cases ((order_iso.to_order_embedding φ) k).2 with i hi,
    use i,
    simp only [e, ψ, hi, hom.to_order_hom_mk, order_iso.coe_to_order_embedding,
      order_embedding.to_order_hom_coe, function.comp_app,
      order_hom.comp_coe, order_hom.coe_fun_mk,
      order_iso.symm_apply_apply, subtype.coe_eta, subtype.val_eq_coe], },
  haveI : strong_epi e := strong_epi_of_epi e,
  exact nonempty.intro
  { I := mk n,
    m := hom.mk (order_hom.comp
      γ (order_embedding.to_order_hom (order_iso.to_order_embedding φ))),
    e := e,
    m_mono := begin
      rw mono_iff_injective,
      intros i₁ i₂ h,
      simp only [hom.to_order_hom_mk, order_iso.coe_to_order_embedding,
        order_embedding.to_order_hom_coe,function.comp_app,  order_hom.comp_coe,
        subtype.val_eq_coe, order_hom.coe_fun_mk, ← subtype.ext_iff] at h,
      exact equiv.injective φ.to_equiv h,
    end, },
end

lemma image_eq {Δ Δ' Δ'' : simplex_category } {φ : Δ ⟶ Δ''}
  {e : Δ ⟶ Δ'} [epi e] {i : Δ' ⟶ Δ''} [mono i] (fac : e ≫ i = φ) :
  image φ = Δ' :=
begin
  haveI := strong_epi_of_epi e,
  let eq := image.iso_strong_epi_mono e i fac,
  ext,
  apply le_antisymm,
  { exact @len_le_of_epi  _ _ eq.hom infer_instance, },
  { exact @len_le_of_mono  _ _ eq.hom infer_instance, },
end

lemma image_ι_eq {Δ Δ'' : simplex_category } {φ : Δ ⟶ Δ''}
  {e : Δ ⟶ image φ} [epi e] {i : image φ ⟶ Δ''} [mono i] (fac : e ≫ i = φ) :
  image.ι φ = i :=
begin
  haveI := strong_epi_of_epi e,
  rw ← image.iso_strong_epi_mono_hom_comp_ι e i fac,
  conv_lhs { rw ← category.id_comp (image.ι φ), },
  congr,
  symmetry,
  apply simplex_category.eq_id_of_is_iso,
  apply_instance,
end

lemma factor_thru_image_eq {Δ Δ'' : simplex_category } {φ : Δ ⟶ Δ''}
  {e : Δ ⟶ image φ} [epi e] {i : image φ ⟶ Δ''} [mono i] (fac : e ≫ i = φ) :
  factor_thru_image φ = e :=
by rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]

end simplex_category
