import category_theory.additive.basic
import category_theory.limits.shapes.images
import category_theory.limits.shapes.strong_epi
import data.sigma.basic
import data.fintype.basic
import dold_kan2

/-!

Goal : 
* construct the inverse functor from chain complexes to simplicial objects (TODO)

-/
universes v u

open classical
noncomputable theory

open category_theory
open category_theory.limits
open opposite
open_locale simplicial

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [additive_category C]

def Γ_index_set (Δ : simplex_category.{v}) := Σ (Δ' : simplex_category.{v}), { α : Δ ⟶ Δ' // epi α }

lemma fintype_Γ_index_set (Δ : simplex_category.{v}) : fintype (Γ_index_set Δ) :=
begin
  apply fintype.of_injective
    ((λ A, ⟨⟨A.1.len,
      nat.lt_succ_iff.mpr (simplex_category.len_le_of_epi A.2.2)⟩, A.2.1.to_order_hom⟩) :
      Γ_index_set Δ → (sigma (λ (k : fin (Δ.len+1)), (fin(Δ.len+1) → fin(k+1))))),
  rintros ⟨Δ₁,α₁'⟩ ⟨Δ₂,α₂'⟩ h,
  simp only at h,
  have eq : Δ₁ = Δ₂ := sorry,
  ext; dsimp,
  { congr', },
  { subst eq,
    apply heq_of_eq,
    rcases α₁' with ⟨α₁,h₁⟩,
    rcases α₂' with ⟨α₂,h₂⟩,
    ext,
    dsimp at h ⊢,
    simp only [fun_like.coe_fn_eq, eq_self_iff_true, heq_iff_eq] at h ⊢,
    rw h.right, }
end

instance : has_strong_epi_mono_factorisations simplex_category.{v} := sorry

instance {Δ : simplex_category} : fintype (Γ_index_set Δ) := fintype_Γ_index_set Δ

def Γ_summand (K : chain_complex C ℕ) (Δ : simplex_category.{v}) 
  (A : Γ_index_set Δ) : C := K.X A.1.len

def Γ_termwise (K : chain_complex C ℕ) (Δ : simplex_category.{v}) : C :=
  ∐ (λ (A : Γ_index_set Δ), K.X A.1.len)

def Γ_on_mono (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i] :
  K.X Δ.len ⟶ K.X Δ'.len :=
begin
  sorry,
end

noncomputable def Γ_simplicial (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (θ : Δ' ⟶ Δ) :
  Γ_termwise K Δ ⟶ Γ_termwise K Δ' :=
begin
  apply sigma.desc,
  intro A,
  let decomp := image.mono_factorisation (θ ≫ A.2.1),
  have strong_decomp : has_strong_epi_mono_factorisations simplex_category.{v} := by apply_instance,
  have has_fac := strong_decomp.has_fac,
  let A' : Γ_index_set Δ' := ⟨decomp.I, ⟨decomp.e,
    (strong_epi_of_strong_epi_mono_factorisation 
    ((classical.choice (has_fac _))) (image.is_image _)).epi⟩⟩,
  exact Γ_on_mono K decomp.m ≫ (sigma.ι (Γ_summand K Δ') A'),
end

def Γ_obj (K : chain_complex C ℕ) : simplicial_object C :=
{ obj := λ Δ, Γ_termwise K (unop Δ),
  map := λ Δ Δ' θ, Γ_simplicial K θ.unop,
  map_id' := sorry,
  map_comp' := sorry, }

#check Γ_obj

end dold_kan

end algebraic_topology
