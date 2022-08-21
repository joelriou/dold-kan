import category_theory.limits.shapes.images
import algebraic_topology.simplex_category
import tactic.equiv_rw
import for_mathlib.lifting_properties_misc
import category_theory.limits.shapes.regular_mono

noncomputable theory

universes u

namespace category_theory

lemma concrete_category.bijective_of_is_iso {C : Type*} [category C]
  [concrete_category C] {X Y : C} (f : X ⟶ Y) [is_iso f] :
  function.bijective ((forget _).map f) :=
by { rw ← is_iso_iff_bijective, apply_instance, }

lemma strong_epi_of_is_split_epi
  {C : Type*} [category C] {A B : C} (f : A ⟶ B) [is_split_epi f] : strong_epi f :=
strong_epi.mk' begin
  introsI X Y z hz u v sq,
  exact comm_sq.has_lift.mk'
  { l := section_ f ≫ u,
    fac_left' := by simp only [← cancel_mono z, sq.w, category.assoc, is_split_epi.id_assoc],
    fac_right' := by simp only [sq.w, category.assoc, is_split_epi.id_assoc], }
end

variables {C D : Type*} [category C] [category D] (F : C ⥤ D) {A B : C} (f : A ⟶ B)

namespace functor

def is_split_epi_iff [full F] [faithful F] : is_split_epi f ↔ is_split_epi (F.map f) :=
begin
  split,
  { intro h, refine is_split_epi.mk' ((split_epi_equiv F f).to_fun h.exists_split_epi.some), },
  { intro h, refine is_split_epi.mk' ((split_epi_equiv F f).inv_fun h.exists_split_epi.some), },
end

variable {F}
lemma strong_epi_imp_strong_epi_map_of_adjunction {F' : D ⥤ C} (adj : F ⊣ F') (f : A ⟶ B)
  [h₁ : preserves_monomorphisms F']
  [h₂ : preserves_epimorphisms F] :
  strong_epi f → strong_epi (F.map f) :=
begin
  introI hf,
  refine ⟨infer_instance, _⟩,
  intros X Y z,
  introI,
  rw has_lifting_property.iff_of_adjunction adj,
  apply_instance,
end

instance strong_epi_map_of_is_equivalence [is_equivalence F]
  [h : strong_epi f] : strong_epi (F.map f) :=
strong_epi_imp_strong_epi_map_of_adjunction ((as_equivalence F).to_adjunction) f h

lemma strong_epi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  (e : arrow.mk f ≅ arrow.mk g) [h : strong_epi f] : strong_epi g :=
{ epi := begin
    haveI : epi (f ≫ (arrow.right_func.map_iso e).hom) := epi_comp _ _,
    have eq : g = (arrow.left_func.map_iso e).inv ≫ f ≫
      (arrow.right_func.map_iso e).hom,
    { have eq' := arrow.hom.congr_right e.inv_hom_id,
      dsimp at eq',
      simp only [map_iso_inv, arrow.left_func_map, map_iso_hom,
        arrow.right_func_map, arrow.w_mk_right_assoc, arrow.mk_hom, eq'],
      dsimp,
      simp only [category.comp_id], },
    rw eq,
    apply epi_comp,
  end,
  llp := λ X Y z, begin
    introI,
    apply has_lifting_property.of_arrow_iso_left e z,
  end }

lemma strong_epi_iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
  (e : arrow.mk f ≅ arrow.mk g) : strong_epi f ↔ strong_epi g :=
by { split; introI, exacts [strong_epi.of_arrow_iso e, strong_epi.of_arrow_iso e.symm], }

def arrow.iso_of_nat_iso {C D : Type*} [category C] [category D]
  {F G : C ⥤ D} (e : F ≅ G) (f : arrow C) :
  F.map_arrow.obj f ≅ G.map_arrow.obj f :=
arrow.iso_mk (e.app f.left) (e.app f.right) (by simp)

variable (F)
lemma strong_epi_iff_strong_epi_map_of_is_equivalence [is_equivalence F] :
  strong_epi f ↔ strong_epi (F.map f) :=
begin
  split,
  { introI,
    apply_instance, },
  { introI,
    have e : arrow.mk f ≅ arrow.mk (F.inv.map (F.map f)) :=
      arrow.iso_of_nat_iso (F.as_equivalence.unit_iso) (arrow.mk f),
    rw strong_epi_iff_of_arrow_iso e,
    apply_instance, }
end

open limits

def preimage_strong_epi_mono_factorisation (s : strong_epi_mono_factorisation (F.map f))
  [is_equivalence F] :
  strong_epi_mono_factorisation f :=
begin
  haveI : mono (F.preimage (F.as_equivalence.counit_iso.hom.app _ ≫ s.m)),
  { simp only [← F.mono_map_iff_mono, as_equivalence_counit, image_preimage],
    apply mono_comp, },
  haveI : strong_epi (F.preimage (s.e ≫ F.as_equivalence.counit_iso.inv.app _)),
  { simp only [F.strong_epi_iff_strong_epi_map_of_is_equivalence,
      image_preimage, as_equivalence_counit],
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
  rw [← simplex_category.skeletal_equivalence.inverse.epi_map_iff_epi,
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
  refine is_split_epi.mk' ⟨⟨φ, _⟩, _⟩, swap,
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

lemma mono_iff_injective {A B : NonemptyFinLinOrd.{u}} {f : A ⟶ B} :
  mono f ↔ function.injective f :=
begin
  have eq := simplex_category.skeletal_equivalence.counit_iso.hom.naturality f,
  simp only [← cancel_mono (simplex_category.skeletal_equivalence.counit_iso.inv.app B),
    category.assoc, iso.hom_inv_id_app, category.comp_id, functor.id_map] at eq,
  rw [← simplex_category.skeletal_equivalence.inverse.mono_map_iff_mono,
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
  rw simplex_category.skeletal_equivalence.{0}.functor.is_split_epi_iff,
  apply is_split_epi_of_epi,
end⟩

instance : strong_epi_category simplex_category :=
⟨λ X Y f, begin
  introI,
  haveI : is_split_epi f := is_split_epi_of_epi f,
  apply strong_epi_of_is_split_epi,
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
