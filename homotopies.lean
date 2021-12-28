/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homotopy

open category_theory
open category_theory.category

namespace homology

variables {C : Type*} [category C] [preadditive C]

/- general stuff on homotopies -/

@[simp]
def null_homotopic_chain_complex_map_f {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) : Π (n : ℕ), K.X n ⟶ L.X n
| 0 := h 0 ≫ L.d 1 0
| (n+1) := h (n+1) ≫ L.d (n+2) (n+1) + K.d (n+1) n ≫ h n

@[simps]
def null_homotopic_chain_complex_map {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) : K ⟶ L :=
{ f := null_homotopic_chain_complex_map_f h,
  comm' := λ i j, begin
    rw complex_shape.down_rel,
    intro hij,
    cases j;
    { rw ← hij, simp, },
  end }

@[simp]
def null_homotopic_chain_complex_map_hom {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) (i j : ℕ) : K.X i ⟶ L.X j :=
begin
  by_cases hij : i+1=j,
  { exact h i ≫ (eq_to_hom (by { congr, assumption, }) : L.X (i+1) ⟶ L.X j) },
  { exact 0 },
end

def homotopy_of_null_homotopic_chain_complex_map {K L : chain_complex C ℕ}
  (h : Π (n : ℕ), K.X n ⟶ L.X (n+1)) :
  homotopy (null_homotopic_chain_complex_map h) 0 :=
{ hom := null_homotopic_chain_complex_map_hom h,
  zero' := λ i j hij, begin
    rw complex_shape.down_rel at hij,
    simp only [null_homotopic_chain_complex_map_hom, dite_eq_right_iff],
    intro hij',
    exfalso,
    exact hij hij',
  end,
  comm := λ n, begin
    cases n,
    { simp, },
    { simp, apply add_comm, }
  end }


@[simps]
def homotopy_add {ι:Type*} {c : complex_shape ι} {K L : homological_complex C c} {f g f' g': K ⟶ L}
  (h : homotopy f g) (h' : homotopy f' g') : homotopy (f+f') (g+g') :=
{ hom := h.hom + h'.hom,
  zero' := λ i j hij, by
    rw [pi.add_apply, pi.add_apply, h.zero' i j hij, h'.zero' i j hij, add_zero],
  comm := λ i, by
    { simp only [homological_complex.add_f_apply, h.comm, h'.comm,
        add_monoid_hom.map_add],
      abel, }, }

lemma mono_of_degreewise_mono {ι:Type*} {c : complex_shape ι} {K L : homological_complex C c} (φ : K ⟶ L) 
(hφ : ∀ (i : ι), mono (φ.f i)) : mono φ :=
{ right_cancellation := λ Z g h H, by
  { ext i,
    have rcancel := (hφ i).right_cancellation,
    apply rcancel (g.f i) (h.f i),
    simp only [← homological_complex.comp_f],
    congr', }, }

def mono_over.mk_from_mono {ι:Type*} {c : complex_shape ι} {K L : homological_complex C c}
(φ : K ⟶ L) (hφ : ∀ (i : ι), mono (φ.f i)) : mono_over L := ⟨over.mk φ, mono_of_degreewise_mono φ hφ⟩

lemma factors_of_degreewise_factors {ι:Type*} {c : complex_shape ι} {K L M : homological_complex C c} 
{φ : K ⟶ L} {g : M ⟶ L} (hφ : ∀ (i : ι), mono (φ.f i)) (hg : ∀ (i : ι), (mono_over.mk' (φ.f i)).factors (g.f i)) :
(mono_over.mk_from_mono φ hφ).factors g :=
begin
  let h : M ⟶ K :=
  { f := λ i, mono_over.factor_thru (mono_over.mk' (φ.f i)) (g.f i) (hg i),
    comm' := λ i j hij, by
    { apply (cancel_mono (φ.f j)).mp,
      slice_lhs 2 3 { rw ← φ.comm' i j hij, },
      sorry, 
    },
  },
  sorry,
end

end homology

