/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ToposPort.SliceClosed

/-! # Products with constant objects in a slice -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u
namespace ToposPort
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
attribute [local instance] Over.cartesianMonoidalCategory

/-- A product with the constant slice object has the expected underlying object. -/
def starProductIso (B A : C) (T : Over B) :
    (((Over.star B).obj A) ⊗ T).left ≅ A ⊗ T.left where
  hom := lift (pullback.fst ((Over.star B).obj A).hom T.hom ≫ Limits.prod.snd)
    (pullback.snd ((Over.star B).obj A).hom T.hom)
  inv := pullback.lift
    (Limits.prod.lift (snd A T.left ≫ T.hom) (fst A T.left))
    (snd A T.left) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply Limits.prod.hom_ext
      · simpa using (pullback.condition (f := ((Over.star B).obj A).hom) (g := T.hom)).symm
      · simp
    · simp
  inv_hom_id := by apply CartesianMonoidalCategory.hom_ext <;> simp

/-- Naturality in the slice object. -/
lemma starProductIso_natural_right (B A : C) {T T' : Over B} (f : T' ⟶ T) :
    (((Over.star B).obj A) ◁ f).left ≫ (starProductIso B A T).hom =
      (starProductIso B A T').hom ≫ (A ◁ f.left) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    dsimp only [starProductIso] <;>
    simp only [Category.assoc, lift_fst, lift_snd, lift_snd_assoc,
      whiskerLeft_fst, whiskerLeft_snd, Over.whiskerLeft_left_fst_assoc,
      Over.whiskerLeft_left_snd]

/-- Naturality in the constant object. -/
lemma starProductIso_natural_left (B : C) {A A' : C} (f : A ⟶ A') (T : Over B) :
    ((Over.star B).map f ▷ T).left ≫ (starProductIso B A' T).hom =
      (starProductIso B A T).hom ≫ (f ▷ T.left) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    dsimp only [starProductIso] <;>
    simp only [Category.assoc, lift_fst, lift_snd, lift_fst_assoc,
      Over.whiskerRight_left_fst_assoc, Over.whiskerRight_left_snd,
      whiskerRight_fst, whiskerRight_snd, Over.star_map_left, Limits.prod.map_snd]

end ToposPort
