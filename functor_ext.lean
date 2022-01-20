import category_theory.functor_category
import category_theory.eq_to_hom

open category_theory

namespace category_theory

lemma functor_ext {D D' : Type*} [category D] [category D'] {F G : D ⥤ D'}
  (h_obj : (∀ (X : D ), F.obj X = G.obj X))
  (h_map : (∀ (X Y : D) (f : X ⟶ Y), F.map f ≫ eq_to_hom (h_obj Y) = eq_to_hom (h_obj X) ≫ G.map f)) :
  F = G :=
begin
  cases F,
  cases G,
  have eq : F_obj = G_obj,
  { ext X, exact h_obj X, },
  subst eq,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext X Y f,
  simpa using h_map X Y f,
end

lemma congr_obj {D D' : Type*} [category D] [category D'] {F G : D ⥤ D'}
(h : F = G) : ∀ X : D, F.obj X = G.obj X :=
by { intro X, rw h, }

end category_theory