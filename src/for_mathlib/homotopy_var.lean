import algebra.homology.homotopy

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

namespace homotopy

--def prehomotopy_comp (hom : (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) (g : D ⟶ E)
--λ ij, hom ij ≫ g.f ij.val.2

lemma null_homotopic_map_comp (hom : Π i j, C.X i ⟶ D.X j) (g : D ⟶ E) :
null_homotopic_map hom ≫ g = null_homotopic_map (λ i j, hom i j ≫ g.f j) :=
begin
  ext n,
  dsimp [null_homotopic_map],
  simp only [preadditive.add_comp, d_next_comp_right, to_prev'_comp_right],
end

lemma null_homotopic_map'_comp (hom : Π i j, c.rel j i → (C.X i ⟶ D.X j)) (g : D ⟶ E) :
null_homotopic_map' hom ≫ g = null_homotopic_map' (λ i j hij, hom i j hij ≫ g.f j) :=
begin
  ext n,
  erw null_homotopic_map_comp,
  congr',
  ext i j,
  split_ifs,
  { refl, },
  { rw zero_comp, },
end

lemma comp_null_homotopic_map (f : C ⟶ D) (hom : Π i j, D.X i ⟶ E.X j) :
f ≫ null_homotopic_map hom = null_homotopic_map (λ i j, f.f i ≫ hom i j) :=
begin
  ext n,
  dsimp [null_homotopic_map],
  simp only [preadditive.comp_add, d_next_comp_left, prev_d_comp_left],
end

lemma comp_null_homotopic_map' (f : C ⟶ D) (hom : Π i j, c.rel j i → (D.X i ⟶ E.X j)) :
f ≫ null_homotopic_map' hom = null_homotopic_map' (λ i j hij, f.f i ≫ hom i j hij) :=
begin
  ext n,
  erw comp_null_homotopic_map,
  congr',
  ext i j,
  split_ifs,
  { refl, },
  { rw comp_zero, },
end

lemma map_null_homotopic_map {W : Type*} [category W] [preadditive W]
  (G : V ⥤ W) [G.additive] (hom : Π i j, C.X i ⟶ D.X j) :
  (G.map_homological_complex c).map (null_homotopic_map hom) =
  null_homotopic_map (λ i j, G.map (hom i j)) :=
begin
  ext i,
  dsimp [null_homotopic_map, d_next, prev_d],
  rcases c.next i with _|⟨inext,wn⟩;
  rcases c.prev i with _|⟨iprev,wp⟩;
  dsimp [d_next, prev_d];
  simp only [G.map_comp, functor.map_zero, functor.map_add],
end

lemma map_null_homotopic_map' {W : Type*} [category W] [preadditive W]
  (G : V ⥤ W) [G.additive] (hom : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (G.map_homological_complex c).map (null_homotopic_map' hom) =
  null_homotopic_map' (λ i j hij, G.map (hom i j hij)) :=
begin
  ext n,
  erw map_null_homotopic_map,
  congr',
  ext i j,
  split_ifs,
  { refl, },
  { rw G.map_zero, }
end

end homotopy
