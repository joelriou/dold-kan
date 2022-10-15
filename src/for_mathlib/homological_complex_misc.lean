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

namespace homological_complex

lemma is_iso_of_components {A B : homological_complex C c} (f : A ⟶ B)
  [∀ (n : ι), is_iso (f.f n)] : is_iso f :=
begin
  convert is_iso.of_iso (homological_complex.hom.iso_of_components (λ n, as_iso (f.f n))
    (by tidy)),
  ext n,
  refl,
end

instance {D : Type*} [category D] [preadditive D]
  {F : C ⥤ D} [F.additive] [full F] [faithful F] :
  reflects_isomorphisms (functor.map_homological_complex F c) :=
⟨λ A B f, begin
  introI,
  suffices : ∀ (n : ι), is_iso (f.f n),
  { haveI := this, apply is_iso_of_components, },
  intro n,
  apply is_iso_of_reflects_iso _ F,
  change is_iso ((homological_complex.eval D c n).map ((F.map_homological_complex c).map f)),
  apply_instance,
end⟩

end homological_complex
