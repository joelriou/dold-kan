import algebraic_topology.simplex_category
import category_theory.limits.shapes.images
universes u v

open category_theory
open category_theory.limits

namespace simplex_category

section epi_mono

/-
      f
x ----->> y
|         |
|u        |v
v    w    v 
a >-----> b
 -/

noncomputable def unique_of_existence_and_uniqueness {X : Type*} (existence : ∃ (x : X), true)
  (uniqueness : ∀ (x y : X), x=y) : unique X :=
let h : nonempty X := exists_true_iff_nonempty.mp existence in
{ default := h.some,
  uniq := λ x, uniqueness x h.some, }

def kind_of_strong_epi_of_function_surjective {X Y : Type*} {f : X → Y} (hf : function.surjective f) 
  {A B : Type*} (u : X → A) (v : Y → B) (w : A → B) (w_inj : function.injective w)
  (h : ∀ (x:X), w (u x) = v (f x)) :
  ∃ g : Y → A, (∀ (x : X), u x = g (f x)) ∧ (∀ (y : Y), v y = w (g y)) :=
begin
  let p : Y → set A := λ y a, ∃ (x:X), a = u(x) ∧ y = f(x),
  have G : Π (y : Y), unique ((p y) : Type*) := begin
    intro y,
    have hpy : nonempty (p y) := begin
      apply exists_true_iff_nonempty.mp,
      cases hf y with x hx,
      use ⟨u x, by { use x, split, refl, exact hx.symm, }⟩,
    end,
    exact {
      default := hpy.some,
      uniq := begin
        intro a,
        simp only [subtype.ext_iff_val],
        rcases a.2 with ⟨x, ⟨hx₁,hx₂⟩⟩,
        rcases hpy.some.2 with ⟨x', ⟨hx'₁,hx'₂⟩⟩,
        have hxx' : w (u x) = w (u x') := by rw [h, h, ← hx₂, ← hx'₂],
        exact ((eq.symm hx₁).congr (eq.symm hx'₁)).mp (w_inj hxx'),
      end, },
  end,
  use λ y, (G y).default,
  split,
  { intro x,
    simpa only [subtype.ext_iff_val]
      using (G (f x)).uniq ⟨u x,by { use x, split; refl, }⟩, },
  { intro y,
    cases (G y).default.2 with x' hx',
    simp only [subtype.val_eq_coe] at hx',
    rw [hx'.left, hx'.right],
    exact (h x').symm, },
end

def canonical_epi_mono_factorisation {x y : simplex_category.{u}} (f : x ⟶ y) :
  mono_factorisation f :=
begin
  let α := { j : fin(y.len+1) //
     ∃ (i : fin(x.len+1)), f.to_order_hom i = j },
  let n := fintype.card α-1,
  have eq : fintype.card α = n+1 := begin
    by_cases fintype.card α ≥ 1,
    { exact (nat.sub_eq_iff_eq_add h).mp rfl, },
    { exfalso,
      simp only [not_le, nat.lt_one_iff, fintype.card_eq_zero_iff] at h,
      apply h.false,
      exact ⟨f.to_order_hom 0, (by use 0)⟩, },
  end,
  let ψ : order_hom (fin (x.len+1)) α := ⟨λ i, ⟨f.to_order_hom i, by use i⟩,
    λ _ _ h, f.to_order_hom.monotone' h⟩,
  let φ := mono_equiv_of_fin α eq,
  let γ : order_hom α (fin (y.len+1)) := ⟨λ j, j.1,
    by { rintros ⟨i₁,_⟩ ⟨i₂,_⟩ h, simpa only using h, }⟩,
  exact
  { I := simplex_category.mk n,
    m := simplex_category.hom.mk (order_hom.comp
      γ (order_embedding.to_order_hom (order_iso.to_order_embedding φ))),
    e := simplex_category.hom.mk (order_hom.comp
      (order_embedding.to_order_hom (order_iso.to_order_embedding φ.symm)) ψ),
    m_mono := begin
      apply mono_iff_injective.mpr,
      intros i₁ i₂ h,
      dsimp,
      simp only [hom.to_order_hom_mk, order_iso.coe_to_order_embedding,
        order_embedding.to_order_hom_coe,function.comp_app,  order_hom.comp_coe,
        subtype.val_eq_coe, order_hom.coe_fun_mk, ← subtype.ext_iff] at h,
      exact equiv.injective φ.to_equiv h,
    end,
    fac' := by { ext i, dsimp,
      simp only [order_iso.apply_symm_apply, hom.to_order_hom_mk,
        order_iso.coe_to_order_embedding, order_embedding.to_order_hom_coe,
        function.comp_app, order_hom.comp_coe, order_hom.coe_fun_mk], }, },
end


end epi_mono

end simplex_category
