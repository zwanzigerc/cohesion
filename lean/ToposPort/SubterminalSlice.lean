import ToposPort.SliceClosed
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Restricting functors and adjunctions to subterminal slices

The forgetful functor from a slice over a subterminal object is fully faithful.
This lets an ambient adjunction restrict whenever both functors carry the
chosen slice bases to isomorphic objects. The restricted unit and counit have
exactly the ambient underlying morphisms.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace ToposPort

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- Apply a functor to a slice object, transporting its base through an isomorphism. -/
abbrev mapOver (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q) : Over P ⥤ Over Q :=
  Over.post F ⋙ Over.map e.hom

@[simp]
lemma mapOver_obj_left (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q) (X : Over P) :
    ((mapOver F e).obj X).left = F.obj X.left := rfl

@[simp]
lemma mapOver_obj_hom (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q) (X : Over P) :
    ((mapOver F e).obj X).hom = F.map X.hom ≫ e.hom := rfl

@[simp]
lemma mapOver_map_left (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q)
    {X Y : Over P} (f : X ⟶ Y) : ((mapOver F e).map f).left = F.map f.left := rfl

/-- Forgetting a restricted functor is definitionally the ambient functor after forgetting. -/
def mapOverForget (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q) :
    mapOver F e ⋙ Over.forget Q ≅ Over.forget P ⋙ F := Iso.refl _

@[simp]
lemma mapOverForget_hom_app (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q)
    (X : Over P) : (mapOverForget F e).hom.app X = 𝟙 (F.obj X.left) := rfl

@[simp]
lemma mapOverForget_inv_app (F : C ⥤ D) {P : C} {Q : D} (e : F.obj P ≅ Q)
    (X : Over P) : (mapOverForget F e).inv.app X = 𝟙 (F.obj X.left) := rfl

/-- Restriction to a slice preserves full faithfulness. -/
def mapOverFullyFaithful {F : C ⥤ D} (hF : F.FullyFaithful)
    {P : C} {Q : D} (e : F.obj P ≅ Q) : (mapOver F e).FullyFaithful :=
  (Functor.FullyFaithful.over P F hF).comp
    (Functor.FullyFaithful.ofFullyFaithful (Over.map e.hom))

/-- An adjunction restricts to slices over subterminal bases. -/
def restrictAdjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {P : C} {Q : D} (hP : IsSubterminal P) (hQ : IsSubterminal Q)
    (eF : F.obj P ≅ Q) (eG : G.obj Q ≅ P) : mapOver F eF ⊣ mapOver G eG :=
  adj.restrictFullyFaithful (subterminalForgetFullyFaithful P hP)
    (subterminalForgetFullyFaithful Q hQ) (Iso.refl _) (Iso.refl _)

@[simp]
lemma restrictAdjunction_unit_left {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {P : C} {Q : D} (hP : IsSubterminal P) (hQ : IsSubterminal Q)
    (eF : F.obj P ≅ Q) (eG : G.obj Q ≅ P) (X : Over P) :
    ((restrictAdjunction adj hP hQ eF eG).unit.app X).left = adj.unit.app X.left := by
  simpa [restrictAdjunction] using
    adj.map_restrictFullyFaithful_unit_app (subterminalForgetFullyFaithful P hP)
      (subterminalForgetFullyFaithful Q hQ) (Iso.refl _) (Iso.refl _)
      (L := mapOver F eF) (R := mapOver G eG) X

@[simp]
lemma restrictAdjunction_counit_left {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {P : C} {Q : D} (hP : IsSubterminal P) (hQ : IsSubterminal Q)
    (eF : F.obj P ≅ Q) (eG : G.obj Q ≅ P) (X : Over Q) :
    ((restrictAdjunction adj hP hQ eF eG).counit.app X).left = adj.counit.app X.left := by
  simpa [restrictAdjunction] using
    adj.map_restrictFullyFaithful_counit_app (subterminalForgetFullyFaithful P hP)
      (subterminalForgetFullyFaithful Q hQ) (Iso.refl _) (Iso.refl _)
      (L := mapOver F eF) (R := mapOver G eG) X

end ToposPort
