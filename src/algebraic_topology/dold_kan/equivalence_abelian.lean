/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_pseudoabelian
import algebraic_topology.dold_kan.normalized

noncomputable theory

open category_theory
open category_theory.category
open category_theory.idempotents

instance additive_of_abelian {D : Type*} [category D] [abelian D] : additive_category D :=
{ to_preadditive := infer_instance,
  to_has_finite_biproducts := infer_instance }

variables {A : Type*} [category A] [abelian A]

namespace category_theory

namespace abelian

namespace dold_kan

open algebraic_topology.dold_kan

def N : simplicial_object A ⥤ chain_complex A ℕ := algebraic_topology.normalized_Moore_complex A
def Γ : chain_complex A ℕ ⥤ simplicial_object A := idempotents.dold_kan.Γ

private def e' := to_karoubi_is_equivalence (chain_complex A ℕ)
private def κ' := to_karoubi (chain_complex A ℕ)
private def κinv' : _ ⥤ chain_complex A ℕ := e'.inverse
private def e := to_karoubi_is_equivalence (simplicial_object A)
private def κ := to_karoubi (simplicial_object A)
private def κinv : _ ⥤ simplicial_object A := e.inverse

lemma comparison_N : (N : simplicial_object A ⥤ _) ≅ idempotents.dold_kan.N :=
begin
  calc N ≅ N ⋙ 𝟭 _ : functor.left_unitor N
  ... ≅ N ⋙ (κ' ⋙ κinv') : iso_whisker_left _ e'.unit_iso
  ... ≅ (N ⋙ κ') ⋙ κinv' : by refl
  ... ≅ N' ⋙ κinv' : iso_whisker_right (N'_equiv_karoubi_normalized A).symm _
  ... ≅ idempotents.dold_kan.N : by refl,
end

def equivalence' : simplicial_object A ≌ chain_complex A ℕ := idempotents.dold_kan.equivalence

#check equivalence'

--@[simps]
/-def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
{ functor := N,
  inverse := Γ,
  unit_iso := ΓN.symm,
  counit_iso := NΓ,
  functor_unit_iso_comp' := λ X, begin
    sorry,
  end, }-/

end dold_kan

end idempotents

end category_theory
end dold_kan

end abelian
#check

end category_theory