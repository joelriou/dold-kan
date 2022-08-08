import algebraic_topology.simplicial_object
import algebraic_topology.simplicial_set

open category_theory category_theory.limits opposite
open_locale simplicial

noncomputable theory

universes w v u

namespace sSet

@[simps]
def binary_product (X Y : sSet) : sSet :=
{ obj := λ Δ, X.obj Δ × Y.obj Δ,
  map := λ Δ₁ Δ₂ θ s, (X.map θ s.1, Y.map θ s.2),
  map_id' := λ Δ, begin
    ext1 x,
    simp only [functor_to_types.map_id_apply, prod.mk.eta, types_id_apply],
  end,
  map_comp' := λ Δ₁ Δ₂ Δ₃ θ₁ θ₂, begin
    ext1 x,
    simp only [functor_to_types.map_comp_apply, types_comp_apply],
  end, }

end sSet

namespace category_theory

namespace simplicial_object

variables {C : Type u} [category.{v} C]

/-def Type_inclusion : Type v ⥤ Type (max w v) :=
{ obj := ulift.{w v},
  map := λ X Y f x, ulift.up (f (ulift.down x)),
  map_id' := λ X, by { ext, refl, },
  map_comp' := λ X Y Z f g, by { ext, refl, }, }

def yoneda' {C : Type u} [category.{v} C] :
  C ⥤ (Cᵒᵖ ⥤ Type (max w v)) :=
yoneda ⋙ (whiskering_right _ _ _).obj Type_inclusion-/

namespace sHom

/-- K ⊗ X ⟶ Y -/
@[ext]
structure bihom (K : sSet.{w}) (X Y : simplicial_object C) :=
(φ : Π Δ, K.obj Δ → (X.obj Δ ⟶ Y.obj Δ))
(naturality' : ∀ (Δ₁ Δ₂ : simplex_categoryᵒᵖ)
  (θ : Δ₁ ⟶ Δ₂) (k : K.obj Δ₁), φ Δ₁ k ≫ Y.map θ = X.map θ ≫ φ Δ₂ (K.map θ k))

namespace bihom

restate_axiom naturality'
attribute [reassoc] naturality

@[simp]
def map₁ {K L : sSet} (α : K ⟶ L) (X Y : simplicial_object C)
  (B : bihom L X Y) : bihom K X Y :=
{ φ := λ Δ k, B.φ Δ (α.app Δ k),
  naturality' := λ Δ₁ Δ₂ θ k, begin
    rw naturality,
    congr,
    exact congr_fun (α.naturality θ).symm k,
  end, }

end bihom

end sHom

@[simps]
def sHom (X Y : simplicial_object C) : sSet.{v} :=
{ obj := λ Δ, sHom.bihom (yoneda.obj Δ.unop) X Y,
  map := λ Δ₁ Δ₂ θ, sHom.bihom.map₁ (yoneda.map θ.unop) X Y,
  map_id' := λ Δ, begin
    rw [unop_id, yoneda.map_id],
    ext,
    simp only [sHom.bihom.map₁, nat_trans.id_app, types_id_apply],
  end,
  map_comp' := λ Δ₁ Δ₂ Δ₃ θ₁ θ₂, begin
    rw [unop_comp, yoneda.map_comp],
    ext,
    simp only [sHom.bihom.map₁, functor_to_types.comp, types_comp_apply],
  end }

def sHom₀ (X Y : simplicial_object C) : (sHom X Y) _[0] ≃ (X ⟶ Y) :=
{ to_fun := λ B,
  { app := λ Δ, B.φ Δ (simplex_category.hom.mk (order_hom.const _ 0)),
    naturality' := λ Δ₁ Δ₂ θ, by simpa only [B.naturality], },
  inv_fun := λ f,
  { φ := λ Δ s, f.app Δ,
    naturality' := λ Δ₁ Δ₂ θ k, by rw f.naturality, },
  left_inv := λ f, begin
    ext Δ k,
    simp only,
    congr,
    ext,
    simp only [fin.coe_fin_one],
  end,
  right_inv := λ B, by { ext Δ, refl, }, }

abbreviation tensor_exists (X : simplicial_object C) (K : sSet) :=
  ∀ (Δ : simplex_categoryᵒᵖ), has_coproduct (λ (k : K.obj Δ), X.obj Δ)

@[simps]
def tensor_sSet (X : simplicial_object C) (K : sSet)
  [tensor_exists X K] : simplicial_object C :=
{ obj := λ Δ, sigma_obj (λ (x : K.obj Δ), X.obj Δ),
  map := λ Δ₁ Δ₂ θ, sigma.desc
    (λ x, X.map θ ≫ sigma.ι (λ (x : K.obj Δ₂), X.obj Δ₂) (K.map θ x)),
  map_id' := λ Δ, begin
    ext k,
    discrete_cases,
    erw [colimit.ι_desc, cofan.mk_ι_app, X.map_id, category.id_comp,
      category.comp_id, K.map_id],
    refl,
  end,
  map_comp' := λ Δ₁ Δ₂ Δ₃ θ₁ θ₂, begin
    ext k,
    discrete_cases,
    rw K.map_comp,
    simpa only [X.map_comp, category.assoc, colimit.ι_desc, cofan.mk_ι_app,
      colimit.ι_desc_assoc],
  end, }

namespace tensor_sSet

@[simps]
def map₂ (X : simplicial_object C) {K L : sSet} (f : K ⟶ L)
  [tensor_exists X K] [tensor_exists X L] :
  X.tensor_sSet K ⟶ X.tensor_sSet L :=
{ app := λ Δ, sigma.desc (λ k, sigma.ι (λ l, X.obj Δ) (f.app Δ k)),
  naturality' := λ Δ₁ Δ₂ θ, begin
    ext k,
    discrete_cases,
    simp only [tensor_sSet_map, colimit.ι_desc_assoc, cofan.mk_ι_app,
      category.assoc, colimit.ι_desc],
    congr,
    exact congr_fun (f.naturality θ) k,
  end, }

lemma map₂_id (X : simplicial_object C) (K : sSet)
  [tensor_exists X K] :
  map₂ X (𝟙 K) = 𝟙 _ :=
begin
  ext k,
  discrete_cases,
  dsimp,
  simp only [colimit.ι_desc, cofan.mk_ι_app, category.comp_id],
end

lemma map₂_comp (X : simplicial_object C) {K L M : sSet} (f₁ : K ⟶ L) (f₂ : L ⟶ M)
  [tensor_exists X K] [tensor_exists X L] [tensor_exists X M] :
  map₂ X (f₁ ≫ f₂) = map₂ X f₁ ≫ map₂ X f₂ :=
begin
  ext k,
  dsimp,
  simp only [colimit.ι_desc, cofan.mk_ι_app, colimit.ι_desc_assoc],
end

@[simps]
def map₁ {X Y : simplicial_object C} (g : X ⟶ Y) (K : sSet)
  [tensor_exists X K] [tensor_exists Y K] :
  X.tensor_sSet K ⟶ Y.tensor_sSet K :=
{ app := λ Δ, limits.sigma.map (λ k, g.app Δ),
  naturality' := λ Δ₁ Δ₂ θ, begin
    ext k,
    simp only [tensor_sSet_map, colimit.ι_desc_assoc, cofan.mk_ι_app,
      category.assoc, ι_colim_map, discrete.nat_trans_app,
      nat_trans.naturality_assoc, ι_colim_map_assoc, colimit.ι_desc],
  end, }

lemma map₁₂ {X Y : simplicial_object C} {K L : sSet} (g : X ⟶ Y) (f : K ⟶ L)
  [tensor_exists X K] [tensor_exists Y K]
  [tensor_exists X L] [tensor_exists Y L] :
  map₁ g K ≫ map₂ Y f = map₂ X f ≫ map₁ g L :=
begin
  ext k,
  simp only [nat_trans.comp_app, map₁_app, map₂_app, ι_colim_map_assoc,
    discrete.nat_trans_app, colimit.ι_desc, cofan.mk_ι_app,
    colimit.ι_desc_assoc, ι_colim_map],
end

lemma map₁_id (X : simplicial_object C) (K : sSet)
  [tensor_exists X K] :
  map₁ (𝟙 X) K = 𝟙 _ :=
begin
  ext k,
  dsimp,
  simp only [ι_colim_map, discrete.nat_trans_app, category.comp_id],
  apply category.id_comp,
end

lemma map₁_comp {X Y Z : simplicial_object C} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (K : sSet)
  [tensor_exists X K] [tensor_exists Y K] [tensor_exists Z K] :
  map₁ (g₁ ≫ g₂) K = map₁ g₁ K ≫ map₁ g₂ K :=
begin
  ext k,
  dsimp,
  simp only [ι_colim_map_assoc, discrete.nat_trans_app, ι_colim_map, category.assoc],
end

@[simps]
def functor [hC : has_coproducts.{w} C] : sSet.{w} ⥤ simplicial_object C ⥤ simplicial_object C :=
{ obj := λ K,
  { obj := λ X, X.tensor_sSet K,
    map := λ X Y g, map₁ g K,
    map_id' := λ X, map₁_id X K,
    map_comp' := λ X Y Z g₁ g₂, map₁_comp g₁ g₂ K, },
  map := λ K L f,
  { app := λ X, map₂ X f,
    naturality' := λ X Y g, map₁₂ g f, },
  map_id' := λ K, by { ext1, ext1 X, exact map₂_id X K, },
  map_comp' := λ K L M f₁ f₂, by { ext1, ext1 X, exact map₂_comp X f₁ f₂, }, }

@[simps]
def universal_property (K : sSet) (X Y : simplicial_object C) [tensor_exists X K] :
  sHom.bihom K X Y ≃ (X.tensor_sSet K ⟶ Y) :=
{ to_fun := λ B,
  { app := λ Δ, sigma.desc (B.φ Δ),
    naturality' := λ Δ₁ Δ₂ θ, begin
      ext k,
      simp only [tensor_sSet_map, colimit.ι_desc_assoc, cofan.mk_ι_app,
        category.assoc, colimit.ι_desc, B.naturality],
    end, },
  inv_fun := λ f,
  { φ := λ Δ k, (by exact sigma.ι (λ l, X.obj Δ) k) ≫ f.app Δ,
    naturality' := λ Δ₁ Δ₂ θ k, by simp only [← f.naturality, category.assoc, tensor_sSet_map,
        colimit.ι_desc_assoc, cofan.mk_ι_app], },
  left_inv := λ B, begin
    ext1,
    simp only [colimit.ι_desc, cofan.mk_ι_app],
  end,
  right_inv := λ f, begin
    ext Δ k,
    discrete_cases,
    simp only [colimit.ι_desc, cofan.mk_ι_app],
  end, }

/- triple functoriality -/

/- compatibility between `universal_property` when K is the terminal object and sHom₀ -/

@[simps]
def binary_product_compatibility (K L : sSet) (X Y : simplicial_object C)
  [tensor_exists Y (K.binary_product L)] [tensor_exists X L]:
  sHom.bihom (K.binary_product L) X Y ≃ sHom.bihom K (X.tensor_sSet L) Y :=
{ to_fun := λ B,
  { φ := λ Δ k, sigma.desc (λ l, B.φ Δ (k, l)),
    naturality' := λ Δ₁ Δ₂ θ k, begin
      ext j,
      discrete_cases,
      simp only [colimit.ι_desc_assoc, cofan.mk_ι_app, tensor_sSet_map,
        category.assoc, colimit.ι_desc, B.naturality, sSet.binary_product_map],
    end, },
  inv_fun := λ B,
  { φ := λ Δ kl, (by exact sigma.ι (λ (l : L.obj Δ), X.obj Δ) kl.2) ≫ B.φ Δ kl.1,
    naturality' := λ Δ₁ Δ₂ θ kl, begin
      simpa only [B.naturality, category.assoc, tensor_sSet_map, colimit.ι_desc_assoc,
        cofan.mk_ι_app],
    end},
  left_inv := λ B, begin
    ext1,
    simp only [colimit.ι_desc, cofan.mk_ι_app, prod.mk.eta],
  end,
  right_inv := λ B, begin
    ext Δ k,
    discrete_cases,
    simp only [colimit.ι_desc, cofan.mk_ι_app],
  end, }

end tensor_sSet

end simplicial_object

end category_theory
