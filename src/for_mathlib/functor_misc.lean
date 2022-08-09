import category_theory.functor.category
import category_theory.eq_to_hom

open category_theory

namespace category_theory

namespace functor

--lemma congr_obj {D D' : Type*} [category D] [category D'] {F G : D ⥤ D'}
--(h : F = G) : ∀ X : D, F.obj X = G.obj X :=
--by { intro X, rw h, }

--lemma congr_map {D D' : Type*} [category D] [category D'] (F : D ⥤ D')
--{X Y : D} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g :=
--by { subst h, }

lemma assoc_eq {C₁ C₂ C₃ C₄ : Type*} [category C₁] [category C₂] [category C₃] [category C₄]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₃ ⥤ C₄) :
  (F ⋙ G) ⋙ H = F ⋙ (G ⋙ H) := rfl

end functor

end category_theory
