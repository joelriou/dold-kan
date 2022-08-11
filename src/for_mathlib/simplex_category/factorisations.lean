import category_theory.limits.shapes.images
import algebraic_topology.simplex_category
import tactic.equiv_rw

noncomputable theory

universes u

namespace category_theory

lemma concrete_category.bijective_of_is_iso {C : Type*} [category C]
  [concrete_category C] {X Y : C} (f : X ⟶ Y) [is_iso f] :
  function.bijective ((forget _).map f) :=
by { rw ← is_iso_iff_bijective, apply_instance, }

lemma strong_epi_of_split_epi
  {C : Type*} [category C] {A B : C} (f : A ⟶ B) [split_epi f] : strong_epi f :=
strong_epi.mk' begin
  introsI X Y z hz u v sq,
  exact comm_sq.has_lift.mk'
  { l := section_ f ≫ u,
    fac_left' := by simp only [← cancel_mono z, sq.w, category.assoc, split_epi.id_assoc],
    fac_right' := by simp only [sq.w, category.assoc, split_epi.id_assoc], }
end

variables {C D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

namespace functor

lemma epi_iff_epi_map [hF₁ : preserves_epimorphisms F] [hF₂ : reflects_epimorphisms F] :
  epi f ↔ epi (F.map f) :=
begin
  split,
  { introI h,
    exact F.map_epi f, },
  { exact F.epi_of_epi_map, },
end

lemma mono_iff_mono_map [hF₁ : preserves_monomorphisms F] [hF₂ : reflects_monomorphisms F] :
  mono f ↔ mono (F.map f) :=
begin
  split,
  { introI h,
    exact F.map_mono f, },
  { exact F.mono_of_mono_map, },
end

@[ext]
lemma split_epi.ext (s₁ s₂ : split_epi f) (h : s₁.section_ = s₂.section_) : s₁ = s₂ :=
begin
  unfreezingI { cases s₁, cases s₂, },
  dsimp at *,
  subst h,
end

def split_epi_equiv [full F] [faithful F] : split_epi f ≃ split_epi (F.map f) :=
{ to_fun := λ s, ⟨F.map s.section_,
    by { rw [← F.map_comp, ← F.map_id], congr' 1, apply split_epi.id, }⟩,
  inv_fun := λ s, begin
    refine ⟨F.preimage s.section_, _⟩,
    apply F.map_injective,
    simp only [map_comp, image_preimage, map_id],
    apply split_epi.id,
  end,
  left_inv := by tidy,
  right_inv := by tidy, }

lemma strong_epi_iff_strong_epi_map [is_equivalence F] :
  strong_epi f ↔ strong_epi (F.map f) :=
begin
  /- weaker assumption : F a un adjoint à droite qui préserve et reflète les mono -/
  split,
  { introI hf,
    constructor,
    { rw ← F.epi_iff_epi_map,
      apply_instance, },
    { introsI W Z g hg,
      constructor,
      intros u v sq,
      let W' := F.inv.obj W,
      let Z' := F.inv.obj Z,
      let g' : W' ⟶ Z' := F.inv.map g,
      let u' : X ⟶ W' := F.preimage (u ≫ F.as_equivalence.counit_iso.inv.app W),
      let v' : Y ⟶ Z' := F.preimage (v ≫ F.as_equivalence.counit_iso.inv.app Z),
      have fac' : u' ≫ g' = f ≫ v',
      { apply F.map_injective,
        simp only [sq.w_assoc, map_comp, image_preimage, is_equivalence.fun_inv_map,
          category.assoc, iso.inv_hom_id_app_assoc], },
      exact comm_sq.has_lift.mk'
      { l := F.map (comm_sq.mk fac').lift ≫ F.as_equivalence.counit_iso.hom.app W,
        fac_left' := begin
          dsimp,
          simp only [←F.map_comp_assoc, comm_sq.fac_left, image_preimage, as_equivalence_counit, category.assoc, iso.inv_hom_id_app],
          dsimp,
          simp only [category.comp_id],
        end,
        fac_right' := begin
          have eq := F.as_equivalence.counit_iso.hom.naturality g,
          dsimp at eq ⊢,
          simp only [category.assoc, ← eq, ← F.map_comp_assoc,
            comm_sq.fac_right, image_preimage, as_equivalence_counit,
            iso.inv_hom_id_app],
          dsimp,
          simp only [category.comp_id],
        end, }, }, },
  { introI hf,
    constructor,
    { rw F.epi_iff_epi_map,
      apply_instance, },
    { introsI W Z g hg,
      constructor,
      intros u v sq,
      have fac' : F.map u ≫ F.map g = F.map f ≫ F.map v,
      { simp only [← F.map_comp, sq.w], },
      exact comm_sq.has_lift.mk'
      { l := F.preimage (comm_sq.mk fac').lift,
        fac_left' := F.map_injective (by simp),
        fac_right' := F.map_injective (by simp), }, }, },
end

open limits

def preimage_strong_epi_mono_factorisation (s : strong_epi_mono_factorisation (F.map f))
  [is_equivalence F] :
  strong_epi_mono_factorisation f :=
begin
  haveI : mono (F.preimage (F.as_equivalence.counit_iso.hom.app _ ≫ s.m)),
  { simp only [F.mono_iff_mono_map, as_equivalence_counit, image_preimage],
    apply mono_comp, },
  haveI : strong_epi (F.preimage (s.e ≫ F.as_equivalence.counit_iso.inv.app _)),
  { simp only [F.strong_epi_iff_strong_epi_map, image_preimage, as_equivalence_counit],
    apply strong_epi_comp, },
  exact
  { I := F.inv.obj s.I,
    m := F.preimage (F.as_equivalence.counit_iso.hom.app _ ≫ s.m),
    e := F.preimage (s.e ≫ F.as_equivalence.counit_iso.inv.app _),
    m_mono := infer_instance,
    fac' := begin
      apply F.map_injective,
      simp only [map_comp, image_preimage, category.assoc, iso.inv_hom_id_app_assoc,
        mono_factorisation.fac],
    end, }
end

lemma has_strong_epi_mono_factorisations_imp [is_equivalence F]
  [h : has_strong_epi_mono_factorisations D] :
  has_strong_epi_mono_factorisations C :=
⟨λ X Y f, begin
  apply nonempty.intro,
  apply F.preimage_strong_epi_mono_factorisation,
  let H := h.has_fac,
  exact (H (F.map f)).some,
end⟩

end functor

end category_theory

open category_theory

namespace simplex_category

lemma skeletal_equivalence.functor.map_eq
  {Δ₁ Δ₂ : simplex_category} (f : Δ₁ ⟶ Δ₂) :
  coe_fn (simplex_category.skeletal_equivalence.{u}.functor.map f) =
    ulift.up ∘ f.to_order_hom ∘ ulift.down := rfl

lemma skeletal_equivalence.functor.surjective_iff_map
  {Δ₁ Δ₂ : simplex_category} (f : Δ₁ ⟶ Δ₂) :
  function.surjective f.to_order_hom ↔
  function.surjective
  (simplex_category.skeletal_equivalence.{u}.functor.map f) :=
by rw [skeletal_equivalence.functor.map_eq,
    function.surjective.of_comp_iff' ulift.up_bijective, function.surjective.of_comp_iff _ ulift.down_surjective]

lemma skeletal_equivalence.functor.injective_iff_map
  {Δ₁ Δ₂ : simplex_category} (f : Δ₁ ⟶ Δ₂) :
  function.injective f.to_order_hom ↔
  function.injective
  (simplex_category.skeletal_equivalence.{u}.functor.map f) :=
by rw [skeletal_equivalence.functor.map_eq, function.injective.of_comp_iff ulift.up_injective,
  function.injective.of_comp_iff' _ ulift.down_bijective]

end simplex_category

namespace NonemptyFinLinOrd

lemma epi_iff_surjective {A B : NonemptyFinLinOrd.{u}} (f : A ⟶ B) :
  epi f ↔ function.surjective f :=
begin
  have eq := simplex_category.skeletal_equivalence.counit_iso.hom.naturality f,
  simp only [← cancel_mono (simplex_category.skeletal_equivalence.counit_iso.inv.app B),
    category.assoc, iso.hom_inv_id_app, category.comp_id, functor.id_map] at eq,
  rw [simplex_category.skeletal_equivalence.inverse.epi_iff_epi_map,
    simplex_category.epi_iff_surjective,
    simplex_category.skeletal_equivalence.functor.surjective_iff_map,
    ← functor.comp_map, eq, coe_comp, coe_comp,
    function.surjective.of_comp_iff, function.surjective.of_comp_iff'],
  { apply concrete_category.bijective_of_is_iso, },
  { apply function.bijective.surjective,
    apply concrete_category.bijective_of_is_iso, },
end

instance : split_epi_category NonemptyFinLinOrd.{u} :=
⟨λ X Y f hf, begin
  have H : ∀ (y : Y), nonempty (f⁻¹' { y }),
  { rw epi_iff_surjective at hf,
    intro y,
    exact nonempty.intro ⟨(hf y).some, (hf y).some_spec⟩, },
  let φ : Y → X := λ y, (H y).some.1,
  have hφ : ∀ (y : Y), f (φ y) = y := λ y, (H y).some.2,
  refine ⟨⟨φ, _⟩, _⟩, swap,
  { ext b,
    apply hφ, },
  { intros a b,
    contrapose,
    intro h,
    simp only [not_le] at h ⊢,
    suffices : b ≤ a,
    { cases this.lt_or_eq with h₁ h₂,
      { assumption, },
      { exfalso,
        simpa only [h₂, lt_self_iff_false] using h, }, },
    simpa only [hφ] using f.monotone (le_of_lt h), },
end⟩

instance : strong_epi_category NonemptyFinLinOrd.{u} :=
⟨λ X Y f, begin
  introI,
  haveI : split_epi f := split_epi_of_epi f,
  apply strong_epi_of_split_epi,
end⟩

lemma mono_iff_injective {A B : NonemptyFinLinOrd.{u}} {f : A ⟶ B} :
  mono f ↔ function.injective f :=
begin
  have eq := simplex_category.skeletal_equivalence.counit_iso.hom.naturality f,
  simp only [← cancel_mono (simplex_category.skeletal_equivalence.counit_iso.inv.app B),
    category.assoc, iso.hom_inv_id_app, category.comp_id, functor.id_map] at eq,
  rw [simplex_category.skeletal_equivalence.inverse.mono_iff_mono_map,
    simplex_category.mono_iff_injective,
    simplex_category.skeletal_equivalence.functor.injective_iff_map,
    ← functor.comp_map, eq, coe_comp, coe_comp,
    function.injective.of_comp_iff', function.injective.of_comp_iff],
  { apply function.bijective.injective,
    apply concrete_category.bijective_of_is_iso, },
  { apply concrete_category.bijective_of_is_iso, },
end

@[protected, simps]
def strong_epi_mono_factorisation {X Y : NonemptyFinLinOrd.{u}} (f : X ⟶ Y) :
  limits.strong_epi_mono_factorisation f :=
begin
  let I : NonemptyFinLinOrd.{u} := ⟨set.image (coe_fn f) ⊤, ⟨⟩⟩,
  let e : X ⟶ I := ⟨λ x, ⟨f x, ⟨x, by tidy⟩⟩, λ x₁ x₂ h, f.monotone h⟩,
  let m : I ⟶ Y := ⟨λ y, y, by tidy⟩,
  haveI : epi e,
  { rw epi_iff_surjective, tidy, },
  haveI : strong_epi e := strong_epi_of_epi e,
  haveI : mono m,
  { rw mono_iff_injective, tidy, },
  exact
  { I := I,
    m := m,
    e := e, },
end

instance : limits.has_strong_epi_mono_factorisations NonemptyFinLinOrd.{u} :=
⟨λ X Y f, nonempty.intro (NonemptyFinLinOrd.strong_epi_mono_factorisation f)⟩

end NonemptyFinLinOrd

namespace simplex_category

open category_theory.limits

instance : split_epi_category simplex_category :=
⟨λ X Y f, begin
  introI,
  equiv_rw simplex_category.skeletal_equivalence.{0}.functor.split_epi_equiv _,
  apply split_epi_of_epi,
end⟩

instance : strong_epi_category simplex_category :=
⟨λ X Y f, begin
  introI,
  haveI : split_epi f := split_epi_of_epi f,
  apply strong_epi_of_split_epi,
end⟩

@[protected]
lemma has_strong_epi_mono_factorisations : has_strong_epi_mono_factorisations simplex_category :=
simplex_category.skeletal_functor.has_strong_epi_mono_factorisations_imp.{0}

attribute [instance] has_strong_epi_mono_factorisations

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
