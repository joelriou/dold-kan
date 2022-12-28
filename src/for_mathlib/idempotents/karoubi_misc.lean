/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi
import algebra.homology.homological_complex

noncomputable theory

open category_theory.category
open category_theory.preadditive
open category_theory.limits
open_locale big_operators

namespace category_theory

variables {C : Type*} [category C]

namespace idempotents

namespace karoubi

--@[simp]
--lemma zsmul_hom [preadditive C] {P Q : karoubi C} (f : P ⟶ Q) (n : ℤ) :
--  (n • f).f = n • f.f :=
--map_zsmul (inclusion_hom P Q) n f

end karoubi

variable (C)

@[simps functor inverse]
def to_karoubi_equivalence [is_idempotent_complete C] : C ≌ karoubi C :=
begin
  haveI := to_karoubi_is_equivalence C,
  exact functor.as_equivalence (to_karoubi C),
end


--instance [preadditive C] [is_idempotent_complete C] :
--  is_idempotent_complete (chain_complex C ℕ) := sorry

end idempotents

end category_theory
