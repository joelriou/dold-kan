/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import for_mathlib.homological_complex_misc
import algebra.homology.homological_complex
import algebra.homology.additive
import for_mathlib.idempotents.functor_extension

noncomputable theory

open category_theory
open category_theory.category
open category_theory.preadditive
open category_theory.idempotents

variables {C : Type*} [category C] [preadditive C]
variables {ι : Type*} {c : complex_shape ι}

namespace category_theory

namespace idempotents

namespace karoubi

namespace homological_complex

variables {P Q : karoubi (homological_complex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc]
lemma p_comp_degreewise : P.p.f n ≫ f.f.f n = f.f.f n :=
homological_complex.congr_hom (p_comp f) n

@[simp, reassoc]
lemma comp_p_degreewise : f.f.f n ≫ Q.p.f n = f.f.f n :=
homological_complex.congr_hom (comp_p f) n

@[reassoc]
lemma p_comm_degreewise : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
homological_complex.congr_hom (p_comm f) n

end homological_complex

end karoubi

namespace karoubi_homological_complex

namespace functor

@[simps]
def obj (P : karoubi (homological_complex C c)) : homological_complex (karoubi C) c :=
{ X := λ n, ⟨P.X.X n, P.p.f n, by simpa only [homological_complex.comp_f]
    using homological_complex.congr_hom P.idem n⟩,
  d := λ i j,
    { f := P.p.f i ≫ P.X.d i j,
      comm := begin
        have h :=  homological_complex.congr_hom P.idem j,
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
  idem := by { ext n, simpa only [karoubi.comp] using (K.X n).idem, }, }

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

def counit_eq : inverse ⋙ functor = 𝟭 (homological_complex (karoubi C) c) :=
begin
  apply functor.ext,
  { intros K L f,
    ext n,
    dsimp [functor.map, inverse.map],
    simp only [karoubi.eq_to_hom_f, functor.obj_X_p, homological_complex.eq_to_hom_f,
      eq_to_hom_refl, comp_id, karoubi.comp, inverse.obj_p_f],
    rw [← karoubi.hom.comm], },
  { intro P,
    apply homological_complex.ext,
    { intros i j hij,
      simp [homological_complex.eq_to_hom_f],
      refl, },
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
          have h := homological_complex.congr_hom P.idem i,
          simp only [homological_complex.comp_f] at h,
          slice_lhs 1 2 { erw h, },
          exact P.p.comm' i j hij,
        end },
      comm := begin
        ext n,
        have h := homological_complex.congr_hom P.idem n,
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
          have h := homological_complex.congr_hom P.idem i,
          simp only [homological_complex.comp_f] at h,
          rw h,
        end },
      comm := begin
        ext n,
        have h := homological_complex.congr_hom P.idem n,
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
      using homological_complex.congr_hom P.idem n,
  end,
  inv_hom_id' := begin
    ext P n,
    dsimp [inverse.obj, functor.obj],
    simpa only [homological_complex.comp_f, karoubi.id_eq, karoubi.comp]
      using homological_complex.congr_hom P.idem n,
  end, }

end karoubi_homological_complex

variables (C) (c)

@[simps]
def karoubi_homological_complex_equivalence :
  karoubi (homological_complex C c) ≌ homological_complex (karoubi C) c :=
{ functor    := karoubi_homological_complex.functor,
  inverse    := karoubi_homological_complex.inverse,
  unit_iso   := karoubi_homological_complex.unit_iso,
  counit_iso := eq_to_iso karoubi_homological_complex.counit_eq,
  functor_unit_iso_comp' := λ P, begin
    ext n,
    dsimp,
    have h := homological_complex.congr_hom P.idem n,
    simpa only [karoubi_homological_complex.unit_iso_hom_app_f_f,
      homological_complex.eq_to_hom_f,
      eq_to_hom_app, karoubi_homological_complex.functor.obj_X_p,
      karoubi_homological_complex.inverse.obj_p_f, eq_to_hom_refl,
      karoubi.id_eq, karoubi_homological_complex.functor.map_f_f,
      karoubi.comp] using h,
  end }

lemma functor.map_homological_complex_id {D : Type*} [category D] [preadditive D] :
  functor.map_homological_complex (𝟭 D) c = 𝟭 _ :=
begin
  apply functor.ext,
  { intros X Y f,
    ext n,
    dsimp,
    simp only [homological_complex.eq_to_hom_f, eq_to_hom_refl],
    erw [id_comp, comp_id], },
  { intro X,
    apply homological_complex.ext,
    { intros i j hij,
      erw [comp_id, id_comp],
      refl, },
    { refl, }, },
end

@[simps]
def nat_iso.map_homological_complex {D E : Type*} [category D] [category E] [preadditive D] [preadditive E]
  {F G : D ⥤ E} [F.additive] [G.additive] (e : F ≅ G) :
    functor.map_homological_complex F c ≅ functor.map_homological_complex G c :=
{ hom := nat_trans.map_homological_complex e.hom c,
  inv := nat_trans.map_homological_complex e.inv c,
  hom_inv_id' := by simpa only [← nat_trans.map_homological_complex_comp, e.hom_inv_id],
  inv_hom_id' := by simpa only [← nat_trans.map_homological_complex_comp, e.inv_hom_id], }

def equivalence.map_homological_complex {D E : Type*} [category D] [category E] [preadditive D] [preadditive E]
(e : D ≌ E) [e.functor.additive] : homological_complex D c ≌ homological_complex E c :=
{ functor := functor.map_homological_complex e.functor c,
  inverse := functor.map_homological_complex e.inverse c,
  unit_iso := eq_to_iso (functor.map_homological_complex_id c).symm ≪≫
      nat_iso.map_homological_complex c e.unit_iso,
  counit_iso := nat_iso.map_homological_complex c e.counit_iso ≪≫
      eq_to_iso (functor.map_homological_complex_id c),
  functor_unit_iso_comp' := λ K, begin
    ext n,
    dsimp,
    simp only [eq_to_hom_app, homological_complex.eq_to_hom_f, eq_to_hom_refl],
    erw [id_comp, comp_id, e.functor_unit_iso_comp],
  end, }

instance [is_idempotent_complete C] : is_idempotent_complete (homological_complex C c) :=
begin
  haveI := (to_karoubi_is_equivalence C),
  let e := (functor.as_equivalence (to_karoubi C)),
  let h : (to_karoubi C).additive := by apply_instance,
  haveI : e.functor.additive := h,
  rw is_idempotent_complete_iff_of_equivalence (equivalence.map_homological_complex c e),
  rw ← is_idempotent_complete_iff_of_equivalence (karoubi_homological_complex_equivalence C c),
  apply_instance,
end

variables (α : Type*) [add_right_cancel_semigroup α] [has_one α]

@[simps]
def karoubi_chain_complex_equivalence :
  karoubi (chain_complex C α) ≌
    chain_complex (karoubi C) α :=
  karoubi_homological_complex_equivalence C (complex_shape.down α)

@[simps]
def karoubi_cochain_complex_equivalence :
  karoubi (cochain_complex C α) ≌
    cochain_complex (karoubi C) α :=
  karoubi_homological_complex_equivalence C (complex_shape.up α)

end idempotents

namespace functor

variables {D : Type*} [category D] [preadditive D]

@[simps]
def map_karoubi_homological_complex (F : C ⥤ D) [F.additive] (c : complex_shape ι) :
  karoubi (homological_complex C c) ⥤ karoubi (homological_complex D c) :=
(functor_extension'' _ _).obj (functor.map_homological_complex F c)

lemma map_homological_complex_karoubi_compatibility
  (F : C ⥤ D) [F.additive] (c : complex_shape ι) :
  to_karoubi _ ⋙ F.map_karoubi_homological_complex c =
  F.map_homological_complex c ⋙ to_karoubi _ :=
begin
  apply functor.ext,
  { intros X Y f,
    ext n,
    dsimp [to_karoubi],
    simp only [karoubi.comp, karoubi.eq_to_hom_f, eq_to_hom_refl, comp_id,
      homological_complex.comp_f, map_karoubi_homological_complex_obj_p_f,
      homological_complex.id_f, map_id, map_homological_complex_map_f],
    erw id_comp, },
  { intro X,
    ext1,
    { erw [id_comp, comp_id],
      ext n,
      dsimp,
      simpa only [F.map_id, homological_complex.id_f], },
    { refl, }, },
end

end functor

end category_theory
