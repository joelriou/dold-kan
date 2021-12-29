/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

/- --> algebra/homology/homotopy.lean -/

import algebra.homology.homotopy

open category_theory

universes v u

namespace homotopy

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]
variables {c : complex_shape ι} {C D E : homological_complex V c}

@[simps]
def add {f₁ g₁ f₂ g₂: C ⟶ D}
  (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁+f₂) (g₁+g₂) :=
{ hom := h₁.hom + h₂.hom,
  zero' := λ i j hij, by
    rw [pi.add_apply, pi.add_apply, h₁.zero' i j hij, h₂.zero' i j hij, add_zero],
  comm := λ i, by
    { simp only [homological_complex.add_f_apply, h₁.comm, h₂.comm,
        add_monoid_hom.map_add],
      abel, }, }

end homotopy

