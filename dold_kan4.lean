import category_theory.additive.basic
import category_theory.limits.shapes.images
import data.sigma.basic
import data.fintype.basic
import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import simplex_category

import dold_kan2
import dold_kan3

/-!

Goal : 
* check that this gives the expected equivalence of categories (TODO)

-/
universes v u

open classical
noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite
open_locale simplicial
open category_theory.pseudoabelian

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]

--lemma eq_of_eq_to_iso

lemma NΓ' : to_karoubi _ ⋙ karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N
  ≅ to_karoubi _ :=
{ hom :=
  { app := λ K,
    { f :=
      { f:= λ n, sigma.desc (λ A, begin
        by_cases A.1.len = n,
        { apply eq_to_hom,
          simp only [to_karoubi_obj_X],
          unfold Γ_summand,
          rw h, },
        { exact 0, }
      end),
        comm' := λ i j hij, begin sorry, end, },
      comm := sorry, },
    naturality' := sorry },
  inv :=
  { app := λ K,
    { f :=
      { f := λ n, sigma.ι (Γ_summand K [n]) (⟨[n], ⟨𝟙 _, by apply_instance⟩⟩),
        comm' := sorry },
      comm := sorry}, },
  hom_inv_id' := begin
    ext K n A,
    simp only [homological_complex.comp_f, cofan.mk_ι_app, colimit.ι_desc_assoc,
      nat_trans.id_app, karoubi.id_eq, karoubi.comp, nat_trans.comp_app],
    dsimp,
    split_ifs,
    { have h' : A = ⟨[n],⟨𝟙 _, by apply_instance⟩⟩ := sorry,
      subst h',
      simp only [id_comp, eq_to_hom_refl],
      cases n,
      { erw [P_infty_termwise, P_deg0_eq, id_comp],
        simp only [discrete.nat_trans_app, ι_colim_map],
        erw [id_comp],
        refl, },
      { rw [← assoc, P_infty_termwise],
        let A : Γ_index_set [n+1] := ⟨[n+1], ⟨𝟙 _, by apply_instance⟩⟩,
        let φ : _ ⟶ (Γ.obj _) _[n+1] := ((sigma.ι (Γ_summand K [n+1]) A)),
        erw P_is_identity_where_faces_vanish (_ : higher_faces_vanish (n+1) φ), swap,
        { refine ⟨_⟩,
          intros j hj,
          let i := simplex_category.δ j.succ,
          haveI : mono i,
          { rw simplex_category.mono_iff_injective,
            exact fin.succ_above_right_injective, },
          erw Γ_simplicial_on_summand K A (show 𝟙 _ ≫ i = i ≫ 𝟙 _, by rw [id_comp, comp_id]),
          rw [Γ_on_mono_eq_zero K i _ _, zero_comp],
          { intro h,
            apply nat.succ_ne_self n,
            have h' := congr_arg simplex_category.len h,
            simpa only [simplex_category.len_mk] using congr_arg simplex_category.len h, },
          { rintro ⟨h₁,h₂⟩,
            erw fin.succ_above_below j.succ 0 (fin.succ_pos j) at h₂,
            simpa only [fin.cast_succ_zero, eq_self_iff_true, not_true, ne.def] using h₂, }, },
        { simp only [discrete.nat_trans_app, ι_colim_map],
          erw [id_comp],
          refl, }, }, },
    { erw [zero_comp],
      sorry, },
  end,
  inv_hom_id' := begin
    ext K n,
    dsimp,
    simpa only [homological_complex.comp_f, cofan.mk_ι_app, karoubi.comp,
      simplex_category.len_mk, eq_self_iff_true, colimit.ι_desc],
  end }

@[simps]
theorem NΓ : karoubi.functor_extension (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N ≅ 𝟭 _ :=
(karoubi.to_karoubi_iso_equiv _ _).inv_fun (NΓ'.trans (eq_to_iso (functor.comp_id _).symm))

#print NΓ

end dold_kan

end algebraic_topology
