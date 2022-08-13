import category_theory.lifting_properties.basic
import category_theory.adjunction.basic

namespace category_theory

namespace arrow
namespace hom

variables {C : Type*} [category C]

lemma congr_left {f g : arrow C} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by rw h
lemma congr_right {f g : arrow C} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.right = φ₂.right := by rw h

end hom
end arrow


open category

variables {C D : Type*} [category C] [category D]
  {G : C ⥤ D} {F : D ⥤ C}

namespace comm_sq

section
variables {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y}
  {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}
  (sq : comm_sq u (G.map i) p v) (adj : G ⊣ F)

include sq adj

def right_adjoint :
  comm_sq (adj.hom_equiv _ _ u) i (F.map p) (adj.hom_equiv _ _ v) :=
⟨begin
  simp only [adjunction.hom_equiv_unit, assoc, ← F.map_comp, sq.w],
  rw [F.map_comp, adjunction.unit_naturality_assoc],
end⟩

def right_adjoint_lift_struct_equiv :
  sq.lift_struct ≃ (sq.right_adjoint adj).lift_struct :=
{ to_fun := λ l,
  { l := adj.hom_equiv _ _ l.l,
    fac_left' := by rw [← adj.hom_equiv_naturality_left, l.fac_left],
    fac_right' := by rw [← adjunction.hom_equiv_naturality_right, l.fac_right], },
  inv_fun := λ l,
  { l := (adj.hom_equiv _ _).symm l.l,
    fac_left' := begin
      rw [← adjunction.hom_equiv_naturality_left_symm, l.fac_left],
      apply (adj.hom_equiv _ _).left_inv,
    end,
    fac_right' := begin
      rw [← adjunction.hom_equiv_naturality_right_symm, l.fac_right],
      apply (adj.hom_equiv _ _).left_inv,
    end, },
  left_inv := by tidy,
  right_inv := by tidy, }

@[simp]
lemma right_adjoint_has_lift_iff :
  has_lift (sq.right_adjoint adj) ↔ has_lift sq :=
begin
  simp only [has_lift.iff],
  split,
  { intro h,
    exact nonempty.intro ((sq.right_adjoint_lift_struct_equiv adj).inv_fun h.some), },
  { intro h,
    exact nonempty.intro (sq.right_adjoint_lift_struct_equiv adj h.some), },
end

instance [has_lift sq] : has_lift (sq.right_adjoint adj) :=
by { rw right_adjoint_has_lift_iff, apply_instance, }

end
section
variables {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y}
  {u : A ⟶ F.obj X} {v : B ⟶ F.obj Y}
  (sq : comm_sq u i (F.map p) v) (adj : G ⊣ F)

include sq adj

def left_adjoint  :
  comm_sq ((adj.hom_equiv _ _).symm u) (G.map i) p
    ((adj.hom_equiv _ _).symm v) :=
⟨begin
  simp only [adjunction.hom_equiv_counit, assoc,
    ← G.map_comp_assoc, ← sq.w],
  rw [G.map_comp, assoc, adjunction.counit_naturality],
end⟩

def left_adjoint_lift_struct_equiv :
  sq.lift_struct ≃ (sq.left_adjoint adj).lift_struct :=
{ to_fun := λ l,
  { l := (adj.hom_equiv _ _).symm l.l,
    fac_left' := by rw [← adj.hom_equiv_naturality_left_symm, l.fac_left],
    fac_right' := by rw [← adj.hom_equiv_naturality_right_symm, l.fac_right], },
  inv_fun := λ l,
  { l := (adj.hom_equiv _ _) l.l,
    fac_left' := begin
      rw [← adj.hom_equiv_naturality_left, l.fac_left],
      apply (adj.hom_equiv _ _).right_inv,
    end,
    fac_right' := begin
      rw [← adj.hom_equiv_naturality_right, l.fac_right],
      apply (adj.hom_equiv _ _).right_inv,
    end, },
  left_inv := by tidy,
  right_inv := by tidy, }

@[simp]
lemma left_adjoint_has_lift_iff :
  has_lift (sq.left_adjoint adj) ↔ has_lift sq :=
begin
  simp only [has_lift.iff],
  split,
  { intro h,
    exact nonempty.intro ((sq.left_adjoint_lift_struct_equiv adj).inv_fun h.some), },
  { intro h,
    exact nonempty.intro (sq.left_adjoint_lift_struct_equiv adj h.some), },
end

end

end comm_sq

namespace has_lifting_property

lemma iff_of_adjunction (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
  has_lifting_property (G.map i) p ↔ has_lifting_property i (F.map p) :=
begin
  split,
  { introI,
    constructor,
    intros f g sq,
    rw ← sq.left_adjoint_has_lift_iff adj,
    apply_instance, },
  { introI,
    constructor,
    intros f g sq,
    rw ← sq.right_adjoint_has_lift_iff adj,
    apply_instance, },
end

lemma of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  (e : arrow.mk i ≅ arrow.mk i') (p : X ⟶ Y)
  [hip : has_lifting_property i p] : has_lifting_property i' p :=
begin
  have eq : i' = (arrow.left_func.map_iso e).inv ≫ i ≫ (arrow.right_func.map_iso e).hom,
  { simp only [functor.map_iso_inv, arrow.left_func_map, functor.map_iso_hom,
      arrow.right_func_map, arrow.w_mk_right_assoc, arrow.mk_hom],
    have eq' := arrow.hom.congr_right e.inv_hom_id,
    dsimp at eq' ⊢,
    rw [eq', category.comp_id], },
  rw eq,
  apply_instance,
end

lemma of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (e : arrow.mk p ≅ arrow.mk p')
  [hip : has_lifting_property i p] : has_lifting_property i p' :=
begin
  have eq : p' = (arrow.left_func.map_iso e).inv ≫ p ≫ (arrow.right_func.map_iso e).hom,
  { simp only [functor.map_iso_inv, arrow.left_func_map, functor.map_iso_hom,
      arrow.right_func_map, arrow.w_mk_right_assoc, arrow.mk_hom],
    have eq' := arrow.hom.congr_right e.inv_hom_id,
    dsimp at eq' ⊢,
    rw [eq', category.comp_id], },
  rw eq,
  apply_instance,
end

lemma iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
  (e : arrow.mk i ≅ arrow.mk i') (p : X ⟶ Y) :
  has_lifting_property i p ↔ has_lifting_property i' p :=
by { split; introI, exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p], }

lemma iff_of_arrow_iso_right {A B X Y X' Y' : C} (i : A ⟶ B) {p : X ⟶ Y} {p' : X' ⟶ Y'}
  (e : arrow.mk p ≅ arrow.mk p') :
  has_lifting_property i p ↔ has_lifting_property i p' :=
by { split; introI, exacts [of_arrow_iso_right i e, of_arrow_iso_right i e.symm], }

end has_lifting_property

end category_theory
