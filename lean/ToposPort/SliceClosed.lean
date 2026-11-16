/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ToposPort.SliceClassifier
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Subterminal

/-!
# Cartesian closure of slices over subterminal objects

A coreflective full subcategory closed under binary products is cartesian
closed whenever the ambient category is. In particular, the open part `C/B`
over a subterminal `B` is cartesian closed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe v₁ v₂ u₁ u₂

namespace ToposPort

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Binary-product-closed coreflective full subcategories inherit cartesian closure. -/
@[instance_reducible]
def monoidalClosedOfCoreflective
    [CartesianMonoidalCategory C] [MonoidalClosed C] [CartesianMonoidalCategory D]
    (i : D ⥤ C) (r : C ⥤ D) (adj : i ⊣ r) (hi : i.FullyFaithful)
    [PreservesLimitsOfShape (Discrete WalkingPair) i] : MonoidalClosed D where
  closed B :=
    { rightAdj := i ⋙ ihom (i.obj B) ⋙ r
      adj := (adj.comp (ihom.adjunction (i.obj B))).restrictFullyFaithful
        (Functor.FullyFaithful.id D) hi
        ((Functor.leftUnitor _).trans (CartesianMonoidalCategory.prodComparisonNatIso i B).symm)
        (Functor.rightUnitor _).symm }

section Subterminal

variable [HasPullbacks C] [CartesianMonoidalCategory C]
variable (B : C) (hB : IsSubterminal B)

attribute [local instance] Over.cartesianMonoidalCategory

/-- The forgetful functor from a slice over a subterminal object is fully faithful. -/
def subterminalForgetFullyFaithful : (Over.forget B).FullyFaithful where
  preimage f := Over.homMk f (hB _ _)

/-- Over a subterminal base, the pullback of two structure maps is their product. -/
def subterminalProductIso (X Y : Over B) :
    (X ⊗ Y).left ≅ X.left ⊗ Y.left where
  hom := lift (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom)
  inv := pullback.lift (fst X.left Y.left) (snd X.left Y.left) (hB _ _)
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply hom_ext <;> simp

include hB in
lemma subterminalForget_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (Over.forget B) := by
  let (X Y : Over B) : IsIso (CartesianMonoidalCategory.prodComparison (Over.forget B) X Y) := by
    change IsIso (lift (pullback.fst X.hom Y.hom) (pullback.snd X.hom Y.hom))
    exact (subterminalProductIso B hB X Y).isIso_hom
  exact preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison _

/-- The slice over a subterminal object of a cartesian closed category is cartesian closed. -/
@[instance_reducible]
def subterminalSliceClosed [MonoidalClosed C] : MonoidalClosed (Over B) := by
  letI := subterminalForget_preservesBinaryProducts B hB
  exact monoidalClosedOfCoreflective (Over.forget B) (Over.star B)
    (Over.forgetAdjStar B) (subterminalForgetFullyFaithful B hB)

end Subterminal

end ToposPort
