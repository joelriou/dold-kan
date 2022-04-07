import algebra.homology.homological_complex
import algebra.homology.additive


open category_theory
open category_theory.category
open category_theory.preadditive

variables {C : Type*} [category C] [preadditive C]
variables {ι : Type*} {c : complex_shape ι}

namespace homological_complex
/-
@[simp]
def eq_to_hom_f {K L : homological_complex C c} (h : K = L) (n : ι) :
  homological_complex.hom.f (eq_to_hom h) n =
  eq_to_hom (congr_fun (congr_arg homological_complex.X h) n) :=
by { subst h, simp only [homological_complex.id_f, eq_to_hom_refl], }

@[ext]
def ext {K L : homological_complex C c} (h_X : K.X = L.X)
  (h_d : ∀ (i j : ι), c.rel i j → K.d i j ≫ eq_to_hom (congr_fun h_X j) =
    eq_to_hom (congr_fun h_X i) ≫ L.d i j) : K = L :=
begin
  cases K,
  cases L,
  dsimp at h_X,
  subst h_X,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext i j,
  by_cases hij : c.rel i j,
  { simpa only [id_comp, eq_to_hom_refl, comp_id] using h_d i j hij, },
  { rw [K_shape' i j hij, L_shape' i j hij], }
end-/

def congr_X {K L : homological_complex C c} (h : K = L) :
  ∀ (n : ι), K.X n = L.X n :=
by { intro n, subst h, }

def congr_d {K L : homological_complex C c} (h : K = L) :
  ∀ (i j : ι), c.rel i j → K.d i j ≫ eq_to_hom (congr_X h j) =
  eq_to_hom (congr_X h i) ≫ L.d i j:=
by { intros i j hij, subst h, simp only [id_comp, eq_to_hom_refl, comp_id], }

end homological_complex

namespace chain_complex

variables {D : Type*} [category D] [preadditive D]
variables {α : Type*} [add_right_cancel_semigroup α] [has_one α] [decidable_eq α]

lemma map_of (F : C ⥤ D) [F.additive] (X : α → C) (d : Π n, X (n+1) ⟶ X n)
  (sq : ∀ n, d (n+1) ≫ d n = 0) :
  (F.map_homological_complex _).obj (chain_complex.of X d sq) =
  chain_complex.of (λ n, F.obj (X n))
    (λ n, F.map (d n)) (λ n, by rw [ ← F.map_comp, sq n, functor.map_zero]) :=
begin
  apply homological_complex.ext,
  intros i j hij,
  { have h : j+1=i := hij,
    subst h,
    simp only [of_d, functor.map_homological_complex_obj_d, id_comp,
      eq_to_hom_refl, comp_id], },
  { refl, }
end

end chain_complex

instance {D : Type*} [category D] [preadditive D]
  {F : C ⥤ D} [F.additive] [full F] [faithful F] : reflects_isomorphisms (functor.map_homological_complex F c) :=
begin
  refine ⟨_⟩,
  intros A B f,
  introI,
  let φ := (F.map_homological_complex c).map f,
  let g : B ⟶ A :=
  { f := λ i, (equiv_of_fully_faithful F).inv_fun ((inv φ).f i),
    comm' := λ i j hij, begin
      apply (equiv_of_fully_faithful F).injective,
      dsimp,
      simp only [functor.image_preimage, functor.map_comp],
      haveI : (split_epi (φ.f i)) :=
      { section_ := (inv φ).f i,
        id' := by simpa only [homological_complex.comp_f]
          using homological_complex.congr_hom (is_iso.inv_hom_id φ) i, },
      haveI : (split_mono (φ.f j)) :=
      { retraction := (inv φ).f j,
        id' := by simpa only [homological_complex.comp_f]
          using homological_complex.congr_hom (is_iso.hom_inv_id φ) j, },
      apply (cancel_epi (φ.f i)).mp,
      apply (cancel_mono (φ.f j)).mp,
      conv { to_lhs, congr, rw ← assoc, congr, rw [← homological_complex.comp_f, is_iso.hom_inv_id], },
      conv { to_rhs, rw assoc, congr, skip, rw assoc, congr, skip, rw [← homological_complex.comp_f, is_iso.inv_hom_id], },
      simp only [functor.map_homological_complex_map_f, homological_complex.id_f, id_comp],
      erw comp_id,
      exact (((functor.map_homological_complex F c).map f).comm' i j hij).symm,
    end },
  refine ⟨_⟩,
  use g,
  split; ext n; apply (equiv_of_fully_faithful F).injective; dsimp,
  { simp only [functor.image_preimage, functor.map_comp,
      ← functor.map_homological_complex_map_f, ← homological_complex.comp_f,
      is_iso.hom_inv_id, homological_complex.id_f, F.map_id], },
  { simpa only [functor.image_preimage, functor.map_comp,
      ← functor.map_homological_complex_map_f, ← homological_complex.comp_f,
      is_iso.inv_hom_id, homological_complex.id_f, F.map_id], }
end
