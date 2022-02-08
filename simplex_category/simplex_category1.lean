import algebraic_topology.simplex_category
import category_theory.limits.shapes.images
import category_theory.limits.shapes.strong_epi
universes u v

open category_theory
open category_theory.category
open category_theory.limits

namespace simplex_category

instance {n : ℕ} {i : fin (n+2)} : mono (δ i) :=
begin
  rw mono_iff_injective,
  exact fin.succ_above_right_injective,
end

instance {n : ℕ} {i : fin (n+1)} : epi (σ i) :=
begin
  rw epi_iff_surjective,
  intro b,
  simp only [σ, mk_hom, hom.to_order_hom_mk, order_hom.coe_fun_mk],
  by_cases b ≤ i,
  { use b,
    rw fin.pred_above_below i b (by simpa only [fin.coe_eq_cast_succ] using h),
    simp only [fin.coe_eq_cast_succ, fin.cast_pred_cast_succ], },
  { use b.succ,
    rw [fin.pred_above_above i b.succ _, fin.pred_succ],
    rw not_le at h,
    rw fin.lt_iff_coe_lt_coe at h ⊢,
    simpa only [fin.coe_succ, fin.coe_cast_succ] using nat.lt.step h, }
end

lemma bijective_of_mono_and_eq {x y : simplex_category.{u}} (i : x ⟶ y) [mono i]
  (hxy : x = y) : function.bijective i.to_order_hom :=
by simpa only [fintype.bijective_iff_injective_and_card i.to_order_hom,
    ← mono_iff_injective, hxy, and_true, eq_self_iff_true]

lemma bijective_of_epi_and_eq {x y : simplex_category.{u}} (e : x ⟶ y) [epi e]
  (hxy : x = y) : function.bijective e.to_order_hom :=
by simpa only [fintype.bijective_iff_surjective_and_card e.to_order_hom,
    ← epi_iff_surjective, hxy, and_true, eq_self_iff_true]

@[simps]
noncomputable def iso_of_bijective {x y : simplex_category.{u}} {f : x ⟶ y}
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

lemma is_iso_of_bijective {x y : simplex_category.{u}} {f : x ⟶ y}
  (hf : function.bijective (f.to_order_hom.to_fun)) : is_iso f :=
begin
  rw [show f = (iso_of_bijective hf).hom, by simp only [iso_of_bijective_hom]],
  apply_instance,
end

@[simp]
def order_iso_of_iso {x y : simplex_category.{u}} (e : x ≅ y) :
  fin (x.len+1) ≃o fin (y.len+1) :=
equiv.to_order_iso
  { to_fun    := e.hom.to_order_hom,
    inv_fun   := e.inv.to_order_hom,
    left_inv  := λ i, by simpa only using congr_arg (λ φ, (hom.to_order_hom φ) i) e.hom_inv_id',
    right_inv := λ i, by simpa only using congr_arg (λ φ, (hom.to_order_hom φ) i) e.inv_hom_id', }
  e.hom.to_order_hom.monotone e.inv.to_order_hom.monotone

lemma iso_eq_iso_refl {x : simplex_category.{u}} (e : x ≅ x) :
  e = iso.refl x :=
begin
  have h : (finset.univ : finset (fin (x.len+1))).card = x.len+1 := finset.card_fin (x.len+1),
  have eq₁ := finset.order_emb_of_fin_unique' h
    (λ i, finset.mem_univ ((order_iso_of_iso e) i)),
  have eq₂ := finset.order_emb_of_fin_unique' h
    (λ i, finset.mem_univ ((order_iso_of_iso (iso.refl x)) i)),
  ext1, ext1,
  convert congr_arg (λ φ, (order_embedding.to_order_hom φ)) (eq₁.trans eq₂.symm),
  ext1, ext1 i,
  refl,
end

lemma eq_to_iso_of_iso {x y : simplex_category.{u}} (e : x ≅ y) :
  e = eq_to_iso (skeletal (nonempty.intro e)) :=
by { have h := skeletal (nonempty.intro e), subst h, dsimp, exact iso_eq_iso_refl e, }

lemma eq_eq_to_hom_of_is_iso {x y : simplex_category.{u}} {f : x ⟶ y} (hf : is_iso f) :
  f = eq_to_hom (skeletal (nonempty.intro (as_iso f))) :=
congr_arg (λ (φ : _ ≅ _), φ.hom) (eq_to_iso_of_iso (as_iso f))

lemma eq_id_of_is_iso {x : simplex_category.{u}} {f : x ⟶ x} (hf : is_iso f) : f = 𝟙 _ :=
by simpa only using eq_eq_to_hom_of_is_iso hf

lemma eq_to_hom_eq {Δ Δ' : simplex_category.{u}} (e : Δ = Δ') (k : fin (Δ.len+1)):
  (hom.to_order_hom (eq_to_hom e)) k =
  ⟨k.val, by { rw ← e, exact fin.is_lt k, }⟩  :=
begin
  subst e,
  simp only [hom.id, order_hom.id_coe, fin.val_eq_coe, id.def, hom.to_order_hom_mk,
    eq_to_hom_refl, fin.eta, small_category_id],
end

lemma factorisation_non_injective' {n : ℕ} {Δ' : simplex_category} (θ : mk (n+1) ⟶ Δ')
  (i : fin (n+1)) (hi : θ.to_order_hom i.cast_succ = θ.to_order_hom i.succ):
  ∃ (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' :=
begin
  use δ i.succ ≫ θ,
  ext1, ext1, ext1 x,
  simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe,
    hom.comp, small_category_comp, σ, mk_hom, order_hom.coe_fun_mk],
  by_cases h' : x ≤ i.cast_succ,
  { rw fin.pred_above_below i x h',
    have eq := fin.cast_succ_cast_pred (gt_of_gt_of_ge (fin.cast_succ_lt_last i) h'),
    erw fin.succ_above_below i.succ x.cast_pred _, swap,
    { rwa [eq, ← fin.le_cast_succ_iff], },
    rw eq, },
  { simp only [not_le] at h',
    let y := x.pred (begin
      intro h,
      rw h at h',
      simpa only [fin.lt_iff_coe_lt_coe, nat.not_lt_zero, fin.coe_zero] using h',
    end),
    simp only [show x = y.succ, by rw fin.succ_pred] at h' ⊢,
    rw [fin.pred_above_above i y.succ h', fin.pred_succ],
    by_cases h'' : y = i,
    { rw h'',
      convert hi.symm,
      erw fin.succ_above_below i.succ _,
      exact fin.lt_succ, },
    { erw fin.succ_above_above i.succ _,
      simp only [fin.lt_iff_coe_lt_coe, fin.le_iff_coe_le_coe,
        fin.coe_succ, fin.coe_cast_succ, nat.lt_succ_iff] at h' ⊢,
      simp only [fin.ext_iff] at h'',
      cases nat.le.dest h' with c hc,
      cases c,
      { exfalso,
        rw [add_zero] at hc,
        rw [hc] at h'',
        exact h'' rfl, },
      { rw ← hc,
        simp only [add_le_add_iff_left, nat.succ_eq_add_one,
          le_add_iff_nonneg_left, zero_le], }, }, }
end

lemma fin.cast_succ_lt_iff_succ_le {n : ℕ} {i : fin n} {j : fin (n+1)} : i.cast_succ < j ↔ i.succ ≤ j :=
begin
  simp only [fin.lt_iff_coe_lt_coe, fin.le_iff_coe_le_coe, fin.coe_succ, fin.coe_cast_succ],
  exact nat.lt_iff_add_one_le,
end

lemma factorisation_non_injective {n : ℕ} {Δ' : simplex_category} (θ : mk (n+1) ⟶ Δ')
  (hθ : ¬function.injective θ.to_order_hom) :
  ∃ (i : fin (n+1)) (θ' : (mk n) ⟶ Δ'), θ = σ i ≫ θ' :=
begin
  simp only [function.injective, exists_prop, not_forall] at hθ,
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ (x y : fin (n+2)), (hom.to_order_hom θ) x = (hom.to_order_hom θ) y ∧ x<y,
  { rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩,
    by_cases x<y,
    { exact ⟨x, y, ⟨h₁, h⟩⟩, },
    { refine ⟨y, x, ⟨h₁.symm, _⟩⟩,
      cases lt_or_eq_of_le (not_lt.mp h) with h' h',
      { exact h', },
      { exfalso,
        exact h₂ h'.symm, }, }, },
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩,
  let z := x.cast_pred,
  simp only [← (show z.cast_succ = x,
    by exact fin.cast_succ_cast_pred (lt_of_lt_of_le h₂ (fin.le_last y)))] at h₁ h₂,
  use z,
  apply factorisation_non_injective',
  rw fin.cast_succ_lt_iff_succ_le at h₂,
  apply le_antisymm,
  { exact θ.to_order_hom.monotone (le_of_lt (fin.cast_succ_lt_succ z)), },
  { rw h₁,
    exact θ.to_order_hom.monotone h₂, },
end

lemma factorisation_non_surjective' {n : ℕ} {Δ : simplex_category} (θ : Δ ⟶ mk (n+1))
  (i : fin (n+2)) (hi : ∀ x, θ.to_order_hom x ≠ i) :
  ∃ (θ' : Δ ⟶ (mk n)), θ = θ' ≫ δ i :=
begin
  by_cases i < fin.last (n+1),
  { use θ ≫ σ (fin.cast_pred i),
    ext1, ext1, ext1 x,
    simp only [hom.to_order_hom_mk, function.comp_app,
      order_hom.comp_coe, hom.comp, small_category_comp],
    by_cases h' : θ.to_order_hom x ≤ i,
    { simp only [σ, mk_hom, hom.to_order_hom_mk, order_hom.coe_fun_mk],
      erw fin.pred_above_below (fin.cast_pred i) (θ.to_order_hom x)
        (by simpa [fin.cast_succ_cast_pred h] using h'),
      erw fin.succ_above_below i, swap,
      { simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ],
        exact lt_of_le_of_lt (fin.coe_cast_pred_le_self _)
          (fin.lt_iff_coe_lt_coe.mp ((ne.le_iff_lt (hi x)).mp h')), },
      rw fin.cast_succ_cast_pred,
      apply lt_of_le_of_lt h' h, },
    { simp only [not_le] at h',
      simp only [σ, mk_hom, hom.to_order_hom_mk, order_hom.coe_fun_mk],
      erw fin.pred_above_above (fin.cast_pred i) (θ.to_order_hom x)
        (by simpa only [fin.cast_succ_cast_pred h] using h'),
      erw fin.succ_above_above i, swap,
      { rw fin.le_iff_coe_le_coe,
        simp only [fin.coe_cast_succ, fin.coe_pred],
        exact nat.le_pred_of_lt (fin.lt_iff_coe_lt_coe.mp h'), },
      rw fin.succ_pred, }, },
  { have h' := le_antisymm (fin.le_last i) (not_lt.mp h),
    subst h',
    use θ ≫ σ (fin.last _),
    ext1, ext1, ext1 x,
    simp only [hom.to_order_hom_mk, function.comp_app,
      order_hom.comp_coe, hom.comp, small_category_comp,
      σ, δ, mk_hom, order_hom.coe_fun_mk,
      order_embedding.to_order_hom_coe,
      fin.pred_above_last, fin.succ_above_last],
    rw [fin.cast_succ_cast_pred],
    exact (ne.le_iff_lt (hi x)).mp (fin.le_last _), },
end

lemma factorisation_non_surjective {n : ℕ} {Δ : simplex_category} (θ : Δ ⟶ mk (n+1))
  (hθ : ¬function.surjective θ.to_order_hom) :
  ∃ (i : fin (n+2)) (θ' : Δ ⟶ (mk n)), θ = θ' ≫ δ i :=
begin
  cases not_forall.mp hθ with i hi,
  rw not_exists at hi,
  use i,
  exact factorisation_non_surjective' θ i hi,
end

lemma epi_eq_σ {n : ℕ} (θ : mk (n+1) ⟶ mk n) [epi θ] :
  ∃ (i : fin (n+1)), θ = σ i :=
begin
  rcases factorisation_non_injective θ _ with ⟨i, θ', h⟩, swap,
  { by_contradiction,
    simpa only [nat.one_ne_zero, add_le_iff_nonpos_right, nonpos_iff_eq_zero]
      using le_of_mono (mono_iff_injective.mpr h), },
  use i,
  haveI : epi (σ i ≫ θ'),
  { rw ← h,
    apply_instance, },
  haveI := category_theory.epi_of_epi (σ i) θ',
  rw [h, eq_id_of_is_iso (is_iso_of_bijective (bijective_of_epi_and_eq θ' rfl)), comp_id],
end

lemma mono_eq_δ {n : ℕ} (θ : mk n ⟶ mk (n+1)) [mono θ] :
  ∃ (i : fin (n+2)), θ = δ i :=
begin
  rcases factorisation_non_surjective θ _ with ⟨i, θ', h⟩, swap,
  { by_contradiction,
    simpa only [add_le_iff_nonpos_right, nonpos_iff_eq_zero]
      using le_of_epi (epi_iff_surjective.mpr h), },
  use i,
  haveI : mono (θ' ≫ δ i),
  { rw ← h,
    apply_instance, },
  haveI := category_theory.mono_of_mono θ' (δ i),
  rw [h, eq_id_of_is_iso (is_iso_of_bijective (bijective_of_mono_and_eq θ' rfl)), id_comp],
end

end simplex_category
