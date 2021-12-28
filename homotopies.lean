/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joël Riou
-/

import algebra.homology.homological_complex
import algebra.homology.homotopy

open category_theory
open category_theory.preadditive
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

end homology
