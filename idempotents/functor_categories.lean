/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.idempotents.karoubi

/-!
# Idempotence completeness of functor categories

-/

open category_theory
open category_theory.category
open category_theory.idempotents.karoubi

namespace category_theory

namespace idempotents

variables {J : Type*} [category J]
variables {C : Type*} [category C]

namespace karoubi_functor_category

@[simps]
def obj (P : karoubi (J ⥤ C)) : J ⥤ karoubi C :=
{ obj := λ j, ⟨P.X.obj j, P.p.app j, congr_app P.idempotence j⟩,
	map := λ j j' φ,
	{ f := P.p.app j ≫ P.X.map φ,
		comm := begin
			simp only [nat_trans.naturality, assoc],
     	have h := congr_app P.idempotence j,
     	rw [nat_trans.comp_app] at h,
     	slice_rhs 1 3 { erw [h, h], },
		end },
	map_id' := λ j, by { ext, simp only [functor.map_id, comp_id, id_eq], },
	map_comp' := λ j j' j'' φ φ', begin
		ext,
   	have h := congr_app P.idempotence j,
   	rw [nat_trans.comp_app] at h,
		simp only [assoc, nat_trans.naturality_assoc, functor.map_comp,
     	comp],
    slice_rhs 1 2 { rw h, },
 	  rw [assoc],
	end  }

@[simps]
def map {P Q : karoubi (J ⥤ C)} (f : P ⟶ Q) :
	obj P ⟶ obj Q :=
{ app := λ j, ⟨f.f.app j, congr_app f.comm j⟩,
	naturality' := λ j j' φ, begin
		ext,
		simp only [comp],
    have h := congr_app (comp_p f) j,
    have h' := congr_app (p_comp f) j',
 	  dsimp at h h' ⊢,
   	slice_rhs 1 2 { erw h, },
   	rw ← P.p.naturality,
   	slice_lhs 2 3 { erw h', },
   	rw f.f.naturality,
	end }

end karoubi_functor_category

def karoubi_functor_category_functor :
	karoubi (J ⥤ C) ⥤ (J ⥤ karoubi C) :=
{ obj := karoubi_functor_category.obj,
	map := λ P Q f, karoubi_functor_category.map f,
	map_id' := λ P,
    by { ext j, simpa only [nat_trans.id_app, id_eq], },
	map_comp' := λ P Q R f g,
		by { ext j, simpa only [comp, nat_trans.comp_app], } }

end idempotents

end category_theory
