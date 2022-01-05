import dold_kan2
import category_theory.additive.basic
import data.sigma.basic
import data.fintype.basic

/-!

Goal : 
* construct the inverse functor from chain complexes to simplicial objects (TODO)

-/

open classical
noncomputable theory

open category_theory
open category_theory.limits
open_locale simplicial

namespace algebraic_topology

namespace dold_kan

variables (C : Type*) [category C] [additive_category C]
variables (U : C)

def Γ_index_set (n : ℕ) := Σ (k : fin(n+1)), { α : [n] ⟶ [k] // epi α }

instance (n : ℕ) : fintype (Γ_index_set n) :=
begin
  let φ : fin(n+1) → Type* := λ k, { α : [n] ⟶ [k] // epi α },
  haveI inst2 : ∀ (k : fin(n+1)), fintype (φ k),
  { intro k,
    apply fintype.of_injective (λ (f : { α : [n] ⟶ [k] // epi α }) (x : fin(n+1)), f.1.to_order_hom x),
    rintros ⟨f₁,_⟩ ⟨f₂,_⟩ h,
    simp only,
    ext1,
    simpa only [fun_like.coe_fn_eq] using h, },
  have : fintype (Σ (k : fin(n+1)), φ k) := by apply_instance,
  assumption,
end

def Γ_obj (K : chain_complex C ℕ) (n : ℕ) : C :=
  ∐ (λ (kα : Γ_index_set n), K.X kα.1.1)

end dold_kan

end algebraic_topology
