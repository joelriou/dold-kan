import category_theory.additive.basic
import category_theory.limits.shapes.images
import category_theory.limits.shapes.strong_epi
import data.sigma.basic
import data.fintype.basic
import dold_kan2
import simplex_category

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
  have eq : Δ₁ = Δ₂ := by { ext, simpa using h.left, },
  ext; dsimp,
  { rw eq, },
  { subst eq,
    apply heq_of_eq,
    rcases α₁' with ⟨α₁,h₁⟩,
    rcases α₂' with ⟨α₂,h₂⟩,
    ext,
    dsimp at h ⊢,
    simp only [fun_like.coe_fn_eq, eq_self_iff_true, heq_iff_eq] at h ⊢,
    rw h.right, }
end

instance {Δ : simplex_category} : fintype (Γ_index_set Δ) := fintype_Γ_index_set Δ

def Γ_summand (K : chain_complex C ℕ) (Δ : simplex_category.{v}) 
  (A : Γ_index_set Δ) : C := K.X A.1.len

def Γ_termwise (K : chain_complex C ℕ) (Δ : simplex_category.{v}) : C :=
  ∐ (λ (A : Γ_index_set Δ), Γ_summand K Δ A)

def is_d0 {Δ' Δ : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i] : Prop :=
  (Δ.len = Δ'.len+1) ∧ (i.to_order_hom 0 ≠ 0)

def Γ_on_mono (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i] :
  K.X Δ.len ⟶ K.X Δ'.len :=
begin
  by_cases  Δ = Δ',
  { apply eq_to_hom,
    congr,
    assumption, },
  { by_cases is_d0 i,
    { exact K.d Δ.len Δ'.len, },
    { exact 0, }, },
end

lemma Γ_on_mono_on_id (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i]
  (hi : Δ = Δ') : Γ_on_mono K i = eq_to_hom (by { congr, assumption, }) :=
by { unfold Γ_on_mono, split_ifs, refl, }

lemma Γ_on_mono_on_d0 (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i]
  (hi : is_d0 i) : Γ_on_mono K i = K.d Δ.len Δ'.len :=
begin
  unfold Γ_on_mono,
  split_ifs,
  { exfalso,
    cases hi with h1 h2,
    rw h at h1,
    linarith, },
  refl,
end

lemma Γ_on_mono_eq_zero (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (i : Δ' ⟶ Δ) [mono i]
  (h1 : ¬ Δ = Δ') (h2 : ¬is_d0 i) : Γ_on_mono K i = 0 :=
by { unfold Γ_on_mono, split_ifs, refl, }

def Γ_on_mono_comp (K : chain_complex C ℕ) {Δ'' Δ' Δ : simplex_category.{v}}
   (i' : Δ'' ⟶ Δ') (i : Δ' ⟶ Δ) [mono i] [mono i'] :
   Γ_on_mono K i ≫ Γ_on_mono K i' = Γ_on_mono K (i' ≫ i) :=
begin
  sorry
end

def Γ_simplicial (K : chain_complex C ℕ) {Δ' Δ : simplex_category.{v}} (θ : Δ' ⟶ Δ) :
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

def Γ_simplicial_on_summand (K : chain_complex C ℕ) {Δ'' Δ' Δ : simplex_category.{v}}
  (A : Γ_index_set Δ) {θ : Δ' ⟶ Δ} {e : Δ' ⟶ Δ''} {i : Δ'' ⟶ A.1} [epi e] [mono i]
  (h : e ≫ i = θ ≫ A.2.1) :
  (sigma.ι (Γ_summand K Δ) A) ≫ Γ_simplicial K θ =
  Γ_on_mono K i ≫ (sigma.ι (Γ_summand K Δ') ⟨Δ'', ⟨e, by apply_instance⟩⟩) :=
by { simp only [Γ_simplicial, cofan.mk_ι_app, colimit.ι_desc],
  congr'; rw simplex_category.mono_factorisation_eq e i h, }

def Γ_obj (K : chain_complex C ℕ) : simplicial_object C :=
{ obj := λ Δ, Γ_termwise K (unop Δ),
  map := λ Δ Δ' θ, Γ_simplicial K θ.unop,
  map_id' := sorry,
  map_comp' := sorry, }

end dold_kan

end algebraic_topology
