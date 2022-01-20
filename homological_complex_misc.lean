import algebra.homology.homological_complex
import algebra.homology.additive


open category_theory
open category_theory.category
open category_theory.preadditive

variables {C : Type*} [category C] [preadditive C]
variables {ι : Type*} {c : complex_shape ι}

namespace homological_complex

@[simp]
def homological_complex.eq_to_hom_f {K L : homological_complex C c} (h : K = L) (n : ι) :
  homological_complex.hom.f (eq_to_hom h) n =
  eq_to_hom (congr_fun (congr_arg homological_complex.X h) n) :=
by { subst h, simp only [homological_complex.id_f, eq_to_hom_refl], }

@[ext]
def homological_complex.ext {K L : homological_complex C c} (h_X : K.X = L.X)
  (h_d : ∀ (i j : ι), K.d i j ≫ eq_to_hom (congr_fun h_X j) =
    eq_to_hom (congr_fun h_X i) ≫ L.d i j) : K = L :=
begin
  cases K,
  cases L,
  dsimp at h_X,
  subst h_X,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext i j,
  simpa only [id_comp, eq_to_hom_refl, comp_id] using h_d i j,
end

end homological_complex
