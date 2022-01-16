/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import category_theory.pseudoabelian.basic
import algebra.homology.homological_complex
import algebra.homology.additive

noncomputable theory

open category_theory
open category_theory.category
open category_theory.preadditive

variables {ι : Type*} {c : complex_shape ι}
variables {C : Type*} [category C] [preadditive C]

namespace category_theory

namespace pseudoabelian

namespace karoubi_homological_complex

namespace functor

@[simps]
def obj (P : karoubi (homological_complex C c)) : homological_complex (karoubi C) c :=
{ X := λ n, ⟨P.X.X n, P.p.f n, by simpa only [homological_complex.comp_f]
    using homological_complex.congr_hom P.idempotence n⟩,
  d := λ i j,
    { f := P.p.f i ≫ P.X.d i j,
      comm := begin
        have h :=  homological_complex.congr_hom P.idempotence j,
        simp only [homological_complex.hom.comm_assoc, assoc, homological_complex.hom.comm,
          homological_complex.comp_f] at h ⊢,
        simp only [h]
      end, },
  shape' := λ i j hij, by simp only [karoubi.hom_eq_zero_iff,
    P.X.shape i j hij, limits.comp_zero],
  d_comp_d' := λ i j k hij hjk, begin 
    simp only [karoubi.hom_eq_zero_iff, karoubi.comp, P.p.comm j k],
    slice_lhs 2 3 { rw P.X.d_comp_d' i j k hij hjk, },
    simp only [limits.comp_zero, limits.zero_comp],
  end, }

@[simps]
def map {P Q : karoubi (homological_complex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q :=
{ f:= λ n,
  { f:= f.f.f n,
    comm := by simpa only [homological_complex.comp_f]
      using homological_complex.congr_hom f.comm n, },
  comm' := λ i j hij, begin
    ext,
    simp only [karoubi.comp, obj_d_f, assoc, ← f.f.comm],
    simp only [← assoc],
    have eq := homological_complex.congr_hom (karoubi.p_comm f) i,
    simp only [homological_complex.comp_f] at eq,
    rw eq,
  end }

end functor

@[simps]
def functor :
  karoubi (homological_complex C c) ⥤ homological_complex (karoubi C) c :=
{ obj := functor.obj,
  map := λ P Q f, functor.map f,
  map_comp' := λ P Q R f f',
    by { ext n, simpa only [karoubi.comp], }, }

namespace inverse

@[simps]
def obj (K : homological_complex (karoubi C) c) : karoubi (homological_complex C c) :=
{ X :=
  { X := λ n, (K.X n).X,
    d := λ i j, (K.d i j).f,
    shape' := λ i j hij, karoubi.hom_eq_zero_iff.mp (K.shape' i j hij),
    d_comp_d' := λ i j k hij hjk, by simpa only [karoubi.comp]
      using karoubi.hom_eq_zero_iff.mp (K.d_comp_d' i j k hij hjk), },
  p :=
    { f := λ n, (K.X n).p,
      comm' := λ i j hij, karoubi.p_comm (K.d i j), },
  idempotence := by { ext n, simpa only [karoubi.comp] using (K.X n).idempotence, }, }

@[simps]
def map {K L : homological_complex (karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L :=
{ f:=
  { f := λ n, (f.f n).f,
    comm' := λ i j hij, by simpa only [karoubi.comp]
      using karoubi.hom_ext.mp (f.comm' i j hij), },
  comm := by { ext n, exact (f.f n).comm, }, }

end inverse

@[simps]
def inverse :
  homological_complex (karoubi C) c ⥤ karoubi (homological_complex C c) :=
{ obj := inverse.obj,
  map := λ K L f, inverse.map f,
  map_comp' := λ K L M f g, by { ext n,
    simp only [karoubi.comp, homological_complex.comp_f, inverse.map_f_f], }, }


lemma functor_ext {D D' : Type*} [category D] [category D'] {F G : D ⥤ D'}
  (h_obj : (∀ (X : D ), F.obj X = G.obj X))
  (h_map : (∀ (X Y : D) (f : X ⟶ Y), F.map f ≫ eq_to_hom (h_obj Y) = eq_to_hom (h_obj X) ≫ G.map f)) :
  F = G :=
begin
  cases F,
  cases G,
  have eq : F_obj = G_obj,
  { ext X, exact h_obj X, },
  subst eq,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext X Y f,
  simpa using h_map X Y f,
end

@[simp]
def homological_complex.eq_to_hom_f {K L : homological_complex C c} (h : K = L) (n : ι) :
  homological_complex.hom.f (eq_to_hom h) n =
  eq_to_hom (congr_fun (congr_arg homological_complex.X h) n) :=
by { subst h, simp only [homological_complex.id_f, eq_to_hom_refl], }

@[ext]
def homological_complex.ext {K L : homological_complex C c} (h_X : K.X = L.X)
  (h_d : ∀ (i j : ι), K.d i j ≫ eq_to_hom (congr_fun h_X j) =
    eq_to_hom (congr_fun h_X i) ≫ L.d i j) : K = L :=
begin
  cases K,
  cases L,
  dsimp at h_X,
  subst h_X,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext i j,
  simpa only [id_comp, eq_to_hom_refl, comp_id] using h_d i j,
end

def counit_eq : inverse ⋙ functor = 𝟭 (homological_complex (karoubi C) c) :=
begin
  apply functor_ext,
  { intros K L f,
    ext n,
    dsimp [functor.map, inverse.map],
    simp only [karoubi.comp, homological_complex.eq_to_hom_f, comp_id,
      karoubi.eq_to_hom_f, functor.obj_X_p, eq_to_hom_refl, inverse.obj_p_f,
      karoubi.p_comm], },
  { intro P,
    ext i j,
    { simp [homological_complex.eq_to_hom_f],
      dsimp,
      slice_lhs 2 3 { erw karoubi.comp_p, }, },
    { ext n,
      { simpa only [id_comp, eq_to_hom_refl, comp_id], },
      { refl, }, }, },
end

@[simps]
def unit_iso : 𝟭 (karoubi (homological_complex C c)) ≅ functor ⋙ inverse :=
{ hom :=
  { app := λ P,
    { f :=
      { f := λ n, P.p.f n,
        comm' := λ i j hij, begin
          dsimp,
          have h := homological_complex.congr_hom P.idempotence i,
          simp only [homological_complex.comp_f] at h,
          slice_lhs 1 2 { erw h, },
          exact P.p.comm' i j hij,
        end },
      comm := begin
        ext n,
        have h := homological_complex.congr_hom P.idempotence n,
        simp only [homological_complex.comp_f] at h,
        dsimp,
        rw [h, h],
      end },
    naturality' := λ X Y f, begin
      ext n,
      have h := homological_complex.congr_hom ((karoubi.p_comm f).symm) n,
      simpa only [functor.map_f_f, homological_complex.comp_f,
        inverse.map_f_f, karoubi.comp] using h,
    end },
  inv := 
  { app := λ P,
    { f :=
      { f := λ n, P.p.f n,
        comm' := λ i j hij, begin
          dsimp,
          slice_rhs 2 3 { rw ← P.p.comm' i j hij, },
          rw ← assoc,
          have h := homological_complex.congr_hom P.idempotence i,
          simp only [homological_complex.comp_f] at h,
          rw h,
        end },
      comm := begin
        ext n,
        have h := homological_complex.congr_hom P.idempotence n,
        simp only [homological_complex.comp_f] at h,
        dsimp,
        rw [h, h],
      end },
    naturality' := λ P Q f, begin
      ext n,
      have h := homological_complex.congr_hom (karoubi.p_comm f).symm n,
      simpa only [functor_map, functor.map_f_f, functor.id_map, functor.comp_map,
        homological_complex.comp_f, inverse.map_f_f, inverse_map, karoubi.comp]
        using h,
    end },
  hom_inv_id' := begin
    ext P n,
    dsimp,
    simpa only [homological_complex.comp_f, karoubi.id_eq, karoubi.comp]
      using homological_complex.congr_hom P.idempotence n,
  end,
  inv_hom_id' := begin
    ext P n,
    dsimp [inverse.obj, functor.obj],
    simpa only [homological_complex.comp_f, karoubi.id_eq, karoubi.comp]
      using homological_complex.congr_hom P.idempotence n,
  end, }

end karoubi_homological_complex

variables (C)

def karoubi_homological_complex_equivalence :
  karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c :=
{ functor   := karoubi_homological_complex.functor,
  inverse    := karoubi_homological_complex.inverse,
  unit_iso   := karoubi_homological_complex.unit_iso,
  counit_iso := eq_to_iso karoubi_homological_complex.counit_eq,
  functor_unit_iso_comp' := λ P, begin
    ext n,
    dsimp,
    have h := homological_complex.congr_hom P.idempotence n,
    simpa only [karoubi_homological_complex.unit_iso_hom_app_f_f,
      karoubi_homological_complex.homological_complex.eq_to_hom_f,
      eq_to_hom_app, karoubi_homological_complex.functor.obj_X_p,
      karoubi_homological_complex.inverse.obj_p_f, eq_to_hom_refl,
      karoubi.id_eq, karoubi_homological_complex.functor.map_f_f,
      karoubi.comp] using h,
  end }

end pseudoabelian

end category_theory
