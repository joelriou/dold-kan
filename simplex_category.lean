import algebraic_topology.simplex_category
import category_theory.limits.shapes.images
import category_theory.limits.shapes.strong_epi
universes u v

open category_theory
open category_theory.limits

namespace simplex_category

section epi_mono

def strong_epi_of_epi {X Y : simplex_category.{u}} (f : X ⟶ Y) [epi f] :
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

def strong_epi_mono_factorisation_of_epi_mono_factorisation
  {x y z : simplex_category.{u}} (f : x ⟶ z) (e : x ⟶ y) (i : y ⟶ z)
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

@[simp]
def order_iso_of_iso {x y : simplex_category.{u}} (e : x ≅ y) :
  fin(x.len+1) ≃o fin(y.len+1) := equiv.to_order_iso
  { to_fun    := e.hom.to_order_hom,
    inv_fun   := e.inv.to_order_hom,
    left_inv  := λ i, begin
      have h := congr_arg (λ φ, (hom.to_order_hom φ) i) e.hom_inv_id',
      simpa using h,
    end,
    right_inv := λ i, begin
      have h := congr_arg (λ φ, (hom.to_order_hom φ) i) e.inv_hom_id',
      simpa using h,
    end, }
    e.hom.to_order_hom.monotone e.inv.to_order_hom.monotone

lemma iso_refl_of_iso {x : simplex_category.{u}} (e : x ≅ x) :
  e = iso.refl x :=
begin
  let X : finset (fin(x.len+1)) := finset.univ,
  let X_card : X.card = x.len+1 := finset.card_fin (x.len+1),
  have eq₁ := finset.order_emb_of_fin_unique'
    X_card (λ i, finset.mem_univ ((order_iso_of_iso e) i)),
  have eq₂ := finset.order_emb_of_fin_unique'
    X_card (λ i, finset.mem_univ ((order_iso_of_iso (iso.refl x)) i)),
  rw ← eq₂ at eq₁,
  ext1, ext1, ext1, ext1 i,
  have h := congr_arg (λ φ, (order_embedding.to_order_hom φ) i) eq₁,
  simpa only using h,
end

lemma eq_id_of_is_iso {x : simplex_category.{u}} {f : x ⟶ x} (hf : is_iso f) : f = 𝟙 _ :=
begin
  haveI := hf,
  simpa only [iso.refl_hom, as_iso_hom] using congr_arg (λ (φ : _ ≅ _), φ.hom) (iso_refl_of_iso (as_iso f)),
end

lemma eq_to_iso_of_iso {x y : simplex_category.{u}} (e : x ≅ y) :
  e = eq_to_iso (skeletal (nonempty.intro e)) :=
by { have h := skeletal (nonempty.intro e), subst h, dsimp, exact iso_refl_of_iso e, }

lemma eq_eq_to_hom_of_is_iso {x y : simplex_category.{u}} {f : x ⟶ y} (hf : is_iso f) :
  f = eq_to_hom (skeletal (nonempty.intro (as_iso f))) :=
congr_arg (λ (φ : _ ≅ _), φ.hom) (eq_to_iso_of_iso (as_iso f))

/- Two mono factorisations satisfying the universal property of
the image are equal. -/
def uniqueness_mono_factorisation {x y : simplex_category.{u}} {f : x ⟶ y}
  (F F' : mono_factorisation f) (hF : is_image F) (hF' : is_image F') :
  F = F' :=
begin
  let eqI := eq_to_iso_of_iso (is_image.iso_ext hF hF'),
  have eqm := is_image.iso_ext_hom_m hF hF',
  rw [eqI, eq_to_iso.hom] at eqm,
  ext1,
  { exact eqm.symm, },
end

def mono_factorisation_eq
  {x y z : simplex_category.{u}} {f : x ⟶ z} (e : x ⟶ y) (i : y ⟶ z)
  [epi e] [mono i] (h : e ≫ i = f) :
  image.mono_factorisation f = { I := y, m := i, e := e, fac' := h, } :=
begin
  apply uniqueness_mono_factorisation,
  { exact image.is_image f, },
  { exact strong_epi_mono_factorisation.to_mono_is_image
    (strong_epi_mono_factorisation_of_epi_mono_factorisation f e i h), },
end

lemma epi_of_mono_factorisation
  {x y : simplex_category.{u}} (f : x ⟶ y) :
  epi (image.mono_factorisation f).e :=
begin
  rw uniqueness_mono_factorisation (image.mono_factorisation f)
    (canonical_strong_epi_mono_factorisation f).to_mono_factorisation
    (image.is_image f) (strong_epi_mono_factorisation.to_mono_is_image _),
  haveI := (canonical_strong_epi_mono_factorisation f).e_strong_epi,
  apply_instance,
end

@[simps]
noncomputable lemma iso_of_bijective {x y : simplex_category.{u}} {f : x ⟶ y}
  (hf : function.bijective (f.to_order_hom.to_fun)) : x ≅ y :=
{ hom := f,
  inv := hom.mk
    { to_fun := function.inv_fun f.to_order_hom.to_fun,
      monotone' := λ y₁ y₂ h, begin
        by_cases h' : y₁ < y₂,
        { by_contradiction h'',
          have ineq := f.to_order_hom.monotone' (le_of_not_ge h''),
          have eq := λ i, function.inv_fun_eq (function.bijective.surjective hf i),
          simp only at eq,
          simp only [eq] at ineq,
          exact not_le.mpr h' ineq, },
        { rw eq_of_le_of_not_lt h h', }
      end, },
  hom_inv_id' := begin
    ext1, ext1, ext1 i,
    apply function.left_inverse_inv_fun (function.bijective.injective hf),
  end,
  inv_hom_id' := begin
    ext1, ext1, ext1 i,
    apply function.right_inverse_inv_fun (function.bijective.surjective hf),
  end, }

def bijective_of_mono_and_eq { x y : simplex_category.{u}} (i : x ⟶ y) [mono i]
  (hxy : x = y) : function.bijective i.to_order_hom :=
begin
  apply (fintype.bijective_iff_injective_and_card i.to_order_hom).mpr,
  split,
  { exact simplex_category.mono_iff_injective.mp (by apply_instance), },
  { congr', },
end

def bijective_of_epi_and_eq {x y : simplex_category.{u}} (e : x ⟶ y) [epi e]
  (hxy : x = y) : function.bijective e.to_order_hom :=
begin
  apply (fintype.bijective_iff_surjective_and_card e.to_order_hom).mpr,
  split,
  { exact simplex_category.epi_iff_surjective.mp (by apply_instance), },
  { congr', },
end

instance {n : ℕ} {i : fin(n+2)} : mono (simplex_category.δ i) :=
begin
  rw simplex_category.mono_iff_injective,
  exact fin.succ_above_right_injective,
end

instance {n : ℕ} {i : fin(n+1)} : epi (simplex_category.σ i) :=
begin
  rw simplex_category.epi_iff_surjective,
  intro b,
  simp [simplex_category.σ],
  by_cases b ≤ i,
  { use b,
    erw fin.pred_above_below i b (by simpa only [fin.coe_eq_cast_succ] using h),
    simp only [fin.coe_eq_cast_succ, fin.cast_pred_cast_succ], },
  { use b.succ,
    erw fin.pred_above_above i b.succ _, swap,
    { rw not_le at h,
      rw fin.lt_iff_coe_lt_coe at h ⊢,
      simp only [fin.coe_succ, fin.coe_cast_succ],
      exact nat.lt.step h, },
    simp only [fin.pred_succ], }
end

lemma factorisation_non_injective {n : ℕ} {Δ' : simplex_category} (θ : mk (n+1) ⟶ Δ')
  (hθ : ¬function.injective θ.to_order_hom) :
  ∃ (i : fin(n+1)) (θ' : (mk n) ⟶ Δ'), θ = simplex_category.σ i ≫ θ' :=
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
  let F : fin((mk n).len+1) →o fin(Δ'.len+1) := ⟨f', _⟩, swap,
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

lemma epi_eq_σ {n : ℕ} (θ : mk (n+1) ⟶ mk n) [epi θ] :
  ∃ (i : fin(n+1)), θ = simplex_category.σ i :=
begin
  rcases factorisation_non_injective θ _ with ⟨i,θ',h⟩, swap,
  { by_contradiction,
    simpa only [nat.one_ne_zero, add_le_iff_nonpos_right, nonpos_iff_eq_zero]
      using le_of_mono (mono_iff_injective.mpr h), },
  use i,
  haveI : epi (σ i ≫ θ'),
  { rw ← h,
    apply_instance, },
  haveI := category_theory.epi_of_epi (σ i) θ',
  have h' := congr_arg (λ (φ : _ ≅ _), φ.hom) (iso_refl_of_iso (iso_of_bijective (bijective_of_epi_and_eq θ' rfl))),
  simp only [iso.refl_hom, iso_of_bijective_hom] at h',
  simpa only [h', category.comp_id] using h,
end

lemma eq_to_hom_eq {Δ Δ' : simplex_category.{u}} (e : Δ = Δ') (k : fin (Δ.len+1)):
  (simplex_category.hom.to_order_hom (eq_to_hom e)) k = ⟨k.val, by { rw ← e, exact fin.is_lt k, }⟩  :=
begin
  subst e,
  simp only [hom.id, order_hom.id_coe, fin.val_eq_coe, id.def, hom.to_order_hom_mk,
    eq_to_hom_refl, fin.eta, small_category_id],
end

end epi_mono

end simplex_category
