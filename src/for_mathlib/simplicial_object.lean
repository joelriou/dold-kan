import algebraic_topology.simplicial_object

open opposite
open_locale simplicial

namespace category_theory

variables {C : Type*} [category C]

namespace simplicial_object

@[simp, reassoc]
lemma naturality_δ {X' X : simplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+2)) :
  X.δ i ≫ f.app (op [n]) = f.app (op [n+1]) ≫ X'.δ i := f.naturality _

@[simp, reassoc]
lemma naturality_σ {X' X : simplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+1)) :
  X.σ i ≫ f.app (op [n+1]) = f.app (op [n]) ≫ X'.σ i := f.naturality _

end simplicial_object

namespace cosimplicial_object

@[simp, reassoc]
lemma naturality_δ {X' X : cosimplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+2)) :
  X.δ i ≫ f.app [n+1] = f.app [n] ≫ X'.δ i := f.naturality _

@[simp, reassoc]
lemma naturality_σ {X' X : cosimplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+1)) :
  X.σ i ≫ f.app [n] = f.app [n+1] ≫ X'.σ i := f.naturality _

end cosimplicial_object

end category_theory
