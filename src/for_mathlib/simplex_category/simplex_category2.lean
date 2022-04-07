import algebraic_topology.simplex_category
import category_theory.limits.shapes.images
import category_theory.limits.shapes.strong_epi
--import simplex_category.simplex_category1

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
    let p : fin (Y.len+1) → set (fin (X.len+1)) := λ y x, f.to_order_hom x = y,
    have exists_lift : ∀ (y : fin (Y.len+1)),
      ∃ (x : fin (X.len+1)), f.to_order_hom x = y := λ y,
    by { cases epi_iff_surjective.mp (show epi f, by apply_instance) y with a ha,
      use a, exact ha, },
    let lift : fin (Y.len+1) → fin (X.len+1) := λ y, classical.some (exists_lift y),
    have hlift : ∀ (y : fin (Y.len+1)), f.to_order_hom (lift y) = y :=
      λ y, classical.some_spec (exists_lift y),
    let γ' : fin (Y.len+1) → fin (A.len+1) := λ y, u.to_order_hom (lift y),
    have hγ' : ∀ (x : fin (X.len+1)), γ' (f.to_order_hom x) = u.to_order_hom x,
    { intro x,
      apply mono_iff_injective.mp hw,
      simp only [comm', hlift], },
    let γ : Y ⟶ A := hom.mk
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
    refine ⟨nonempty.intro { lift := γ, fac_left' := _, fac_right' := _, }⟩,
    { ext1, ext1, ext1 x,
      exact hγ' x, },
    { ext y,
      dsimp,
      rw [← hlift y, hγ', comm'], },
  end }

def strong_epi_mono_factorisation_of_epi_mono_factorisation
  {x y z : simplex_category} (f : x ⟶ z) (e : x ⟶ y) (i : y ⟶ z)
  [epi e] [mono i] (h : e ≫ i = f) : strong_epi_mono_factorisation f :=
begin
  haveI : strong_epi e := strong_epi_of_epi e,
  exact
{ I := y,
  m := i,
  e := e,
  m_mono := by apply_instance,
  fac' := h, },
end

def canonical_strong_epi_mono_factorisation {x y : simplex_category} (f : x ⟶ y) :
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
  exact
  { I := mk n,
    m := hom.mk (order_hom.comp
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
      simpa only [order_iso.apply_symm_apply, hom.to_order_hom_mk,
        order_iso.coe_to_order_embedding, order_embedding.to_order_hom_coe,
        function.comp_app, order_hom.comp_coe, order_hom.coe_fun_mk], }, },
end

instance : has_strong_epi_mono_factorisations simplex_category :=
  has_strong_epi_mono_factorisations.mk
  (λ _ _ f, canonical_strong_epi_mono_factorisation f)

lemma eq_of_is_iso {x y : simplex_category} {f : x ⟶ y} (hf : is_iso f) : x = y :=
begin
  ext,
  apply le_antisymm,
  { exact len_le_of_mono (show mono f, by apply_instance), },
  { exact len_le_of_epi (show epi f, by apply_instance), },
end

lemma eq_eq_to_hom_of_is_iso {x y : simplex_category} {f : x ⟶ y} (hf : is_iso f) :
  f = eq_to_hom (eq_of_is_iso hf) :=
begin
  have h := eq_of_is_iso hf,
  unfreezingI { subst h, },
  exact eq_id_of_is_iso hf,
end

/- Two mono factorisations satisfying the universal property of
the image are equal. -/
def uniqueness_mono_factorisation {x y : simplex_category} {f : x ⟶ y}
  (F F' : mono_factorisation f) (hF : is_image F) (hF' : is_image F') :
  F = F' :=
begin
  let eqI := eq_eq_to_hom_of_is_iso (show is_iso (is_image.iso_ext hF hF').hom, by apply_instance),
  have eqm := is_image.iso_ext_hom_m hF hF',
  rw [eqI] at eqm,
  ext1,
  { exact eqm.symm, },
end

def mono_factorisation_eq
  {x y z : simplex_category} {f : x ⟶ z} (e : x ⟶ y) (i : y ⟶ z)
  [epi e] [mono i] (h : e ≫ i = f) :
  image.mono_factorisation f = { I := y, m := i, e := e, fac' := h, } :=
begin
  apply uniqueness_mono_factorisation,
  { exact image.is_image f, },
  { exact strong_epi_mono_factorisation.to_mono_is_image
    (strong_epi_mono_factorisation_of_epi_mono_factorisation f e i h), },
end

lemma epi_of_mono_factorisation
  {x y : simplex_category} (f : x ⟶ y) :
  epi (image.mono_factorisation f).e :=
begin
  rw uniqueness_mono_factorisation (image.mono_factorisation f)
    (canonical_strong_epi_mono_factorisation f).to_mono_factorisation
    (image.is_image f) (strong_epi_mono_factorisation.to_mono_is_image _),
  haveI := (canonical_strong_epi_mono_factorisation f).e_strong_epi,
  apply_instance,
end

end simplex_category
