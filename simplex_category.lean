import algebraic_topology.simplex_category
import category_theory.limits.shapes.images
universes u v

open category_theory
open category_theory.limits

namespace simplex_category

section epi_mono

def strong_epi_of_epi {X Y : simplex_category.{u}} {f : X ⟶ Y}  (hf : epi f) :
  strong_epi f :=
{ epi := hf,
  has_lift := λ A B u v w hw comm,
  begin
    have comm' := λ (x : fin (X.len+1)), congr_arg (λ F, hom.to_order_hom F x) comm,
    simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe,
      hom.comp, small_category_comp] at comm',
    let p : fin (Y.len+1) → set (fin (X.len+1)) := λ y x, f.to_order_hom x = y,
    have exists_lift : ∀ (y : fin (Y.len+1)),
      ∃ (x : fin (X.len+1)), f.to_order_hom x = y := λ y,
    by { cases epi_iff_surjective.mp hf y with a ha, use a, exact ha, },
    let lift : fin (Y.len+1) → fin (X.len+1) := λ y, classical.some (exists_lift y),
    have hlift : ∀ (y : fin (Y.len+1)), f.to_order_hom (lift y) = y :=
      λ y, classical.some_spec (exists_lift y),
    let γ' : fin (Y.len+1) → fin (A.len+1) := λ y, u.to_order_hom (lift y),
    have hγ' : ∀ (x : fin (X.len+1)), γ' (f.to_order_hom x) = u.to_order_hom x,
    { intro x,
      apply mono_iff_injective.mp hw,
      simp only [comm', hlift], },
    let γ : Y ⟶ A := simplex_category.hom.mk
      { to_fun := γ',
        monotone' := λ y₁ y₂ h, begin
          cases eq_or_lt_of_le h with h' h',
          { rw h', },
          { apply (hom.to_order_hom u).monotone',
            by_contradiction h'',
            have ineq := (hom.to_order_hom f).monotone' (le_of_lt (not_le.mp h'')),
            simp only [hlift, order_hom.to_fun_eq_coe] at ineq,
            rw [le_antisymm h ineq] at h',
            exact (irrefl y₂ : ¬(y₂<y₂)) h', },
        end, },
    use {
      lift := γ,
      fac_left' := begin
        ext x,
        dsimp,
        simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe,
          order_hom.coe_fun_mk, hγ'],
      end,
      fac_right' := begin
        ext y,
      dsimp,
      simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe,
        order_hom.coe_fun_mk],
      rw [← hlift y, hγ', comm'],
      end, },
  end }

def canonical_strong_epi_mono_factorisation {x y : simplex_category.{u}} (f : x ⟶ y) :
  strong_epi_mono_factorisation f :=
begin
  let α := { j : fin(y.len+1) // ∃ (i : fin(x.len+1)), f.to_order_hom i = j },
  let n := fintype.card α-1,
  have eq : fintype.card α = n+1 := begin
    by_cases fintype.card α ≥ 1,
    { exact (nat.sub_eq_iff_eq_add h).mp rfl, },
    { exfalso,
      simp only [not_le, nat.lt_one_iff, fintype.card_eq_zero_iff] at h,
      apply h.false,
      exact ⟨f.to_order_hom 0, (by use 0)⟩, },
  end,
  let ψ : order_hom (fin (x.len+1)) α := ⟨λ i, ⟨f.to_order_hom i, by use i⟩,
    λ _ _ h, f.to_order_hom.monotone' h⟩,
  let φ := mono_equiv_of_fin α eq,
  let γ : order_hom α (fin (y.len+1)) := ⟨λ j, j.1,
    by { rintros ⟨i₁,_⟩ ⟨i₂,_⟩ h, simpa only using h, }⟩,
  let e : x ⟶ simplex_category.mk n := simplex_category.hom.mk (order_hom.comp
      (order_embedding.to_order_hom (order_iso.to_order_embedding φ.symm)) ψ), 
  haveI : strong_epi e := strong_epi_of_epi (begin 
    apply epi_iff_surjective.mpr,
    intro k,
    cases ((order_iso.to_order_embedding φ) k).2 with i hi,
    use i,
    simp only [e, ψ, hi, hom.to_order_hom_mk, order_iso.coe_to_order_embedding,
      order_embedding.to_order_hom_coe, function.comp_app,
      order_hom.comp_coe, order_hom.coe_fun_mk,
      order_iso.symm_apply_apply, subtype.coe_eta, subtype.val_eq_coe],
  end),
  exact
  { I := simplex_category.mk n,
    m := simplex_category.hom.mk (order_hom.comp
      γ (order_embedding.to_order_hom (order_iso.to_order_embedding φ))),
    e := e,
    m_mono := begin
      apply mono_iff_injective.mpr,
      intros i₁ i₂ h,
      dsimp,
      simp only [hom.to_order_hom_mk, order_iso.coe_to_order_embedding,
        order_embedding.to_order_hom_coe,function.comp_app,  order_hom.comp_coe,
        subtype.val_eq_coe, order_hom.coe_fun_mk, ← subtype.ext_iff] at h,
      exact equiv.injective φ.to_equiv h,
    end,
    fac' := by { ext i, dsimp,
      simp only [order_iso.apply_symm_apply, hom.to_order_hom_mk,
        order_iso.coe_to_order_embedding, order_embedding.to_order_hom_coe,
        function.comp_app, order_hom.comp_coe, order_hom.coe_fun_mk], }, },
end

instance : has_strong_epi_mono_factorisations simplex_category.{v} :=
  has_strong_epi_mono_factorisations.mk
  (λ _ _ f, canonical_strong_epi_mono_factorisation f)

end epi_mono

end simplex_category
