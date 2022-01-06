import algebraic_topology.simplex_category
import category_theory.limits.shapes.images
import category_theory.limits.shapes.strong_epi

universes u v

open category_theory
open category_theory.limits

namespace simplex_category

section epi_mono

/-
      f
x ----->> y
|         |
|u        |v
v    w    v 
a >-----> b
 -/

def kind_of_strong_epi_of_function_surjective {X Y : Type*} {f : X → Y} (hf : function.surjective f) 
  {A B : Type*} (u : X → A) (v : Y → B) (w : A → B) (w_inj : function.injective w)
  (h : ∀ (x:X), w (u x) = v (f x)) :
  ∃ g : Y → A, (∀ (x : X), u x = g (f x)) ∧ (∀ (y : Y), v y = w (g y)) :=
begin
  let p : Y → set A := λ y a, ∃ (x:X), a = u(x) ∧ y = f(x),
  have G : Π (y : Y), unique ((p y) : Type*) := begin
    intro y,
    sorry,
  end,
  use λ y, (G y).default,
  split,
  { intro x,
    simpa only [subtype.ext_iff_val]
      using (G (f x)).uniq ⟨u x,by { use x, split; refl, }⟩, },
  { intro y,
    have eq : p y ((G y).default) := (G y).default.2,
    cases eq with x' hx',
    rw [hx'.left, hx'.right],
    exact (h x').symm, },
end

def strong_epi_of_epi {x y : simplex_category.{u}} {f : x ⟶ y} (h : epi f) :
  strong_epi f :=
{ epi := h,
  has_lift := λ a b u v w w_mono h,
  begin
    let g : y ⟶ a := simplex_category.hom.mk {
      to_fun := λ i, begin
        let j := v.to_order_hom i,
        sorry,
      end,
      monotone' := sorry,
    },
    sorry,
  end,
}

def unique_strong_epi_mono_factorisation {x y : simplex_category.{u}} (f : x ⟶ y) :
  strong_epi_mono_factorisation f :=
begin
  sorry,
end

instance : has_strong_epi_mono_factorisations simplex_category.{v} :=
has_strong_epi_mono_factorisations.mk (λ _ _, unique_strong_epi_mono_factorisation)



end epi_mono

end simplex_category
