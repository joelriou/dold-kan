/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_pseudoabelian
import algebraic_topology.dold_kan.normalized

/-!

# The Dold-Kan correspondence

The Dold-Kan correspondance states that for any abelian category `A`, there is
an equivalence between the category of simplicial objects in `A` and the
category of chain complexes in `A` (with degrees indexed by `ℕ` and the
homological convention that the degree is decreased by the differentials).

More generally, this results holds for pseudo-abelian categories. Taking this
into consideration, the strategy of proof that is used here is to state and
prove most of the technical results without referring to notions of kernel,
images, etc. The core of the arguments shall be constructing morphisms and
check equalities between morphisms. The applications to abelian categories
are handled at the very end of the proof.

The overall plan is as follows:

* show that the normalized Moore complex is an homotopy equivalent direct factor of
the alternating face map complex, see `P_infty`
and `homotopy_equiv_inclusion_of_Moore_complex`
* show that a morphism of simplicial objects is an isomorphisms if and only if it
induces an isomorphism on normalized Moore complexes
* construct the inverse functor from chain complexes to simplicial objects
* check that this gives the expected equivalence of categories

## References
* Albrecht Dold, Homology of Symmetric Products and Other Functors of Complexes,
Annals of Mathematics, Second Series, Vol. 68 No. 1 (Jul. 1958), pp. 54-80.
* Paul G. Goerss, John F. Jardine, Simplical Homotopy Theory, Modern Birkhäuser Classics,
Reprint of the 1999 edition.

-/


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

@[simps]
def comparison_N : (N : simplicial_object A ⥤ _) ≅ idempotents.dold_kan.N :=
begin
  calc N ≅ N ⋙ 𝟭 _ : functor.left_unitor N
  ... ≅ N ⋙ (κ' ⋙ κinv') : iso_whisker_left _ e'.unit_iso
  ... ≅ (N ⋙ κ') ⋙ κinv' : by refl
  ... ≅ N' ⋙ κinv' : iso_whisker_right (N'_equiv_karoubi_normalized A).symm _
  ... ≅ idempotents.dold_kan.N : by refl,
end

def equivalence : simplicial_object A ≌ chain_complex A ℕ :=
begin
  let F : simplicial_object A ⥤ _ := idempotents.dold_kan.N,
  let hF : is_equivalence F := is_equivalence.of_equivalence idempotents.dold_kan.equivalence,
  letI : is_equivalence (N : simplicial_object A ⥤ _ ) :=
    is_equivalence_of_iso comparison_N.symm hF,
  exact N.as_equivalence,
end

@[simp]
lemma equivalence_functor : (equivalence : simplicial_object A ≌ _).functor = N := by refl

@[simp]
lemma equivalence_inverse : (equivalence : simplicial_object A ≌ _).inverse = Γ := by refl

end dold_kan

end abelian

end category_theory