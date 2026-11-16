import ToposPort.ClosedConservativity
import Mathlib.CategoryTheory.Monoidal.Closed.Ideal

/-!
# Limit properties of the closed reflection

The exponential-ideal argument for finite products is the one used by
Bhavik Mehta's Lean 3 `topos` project (`src/sheaf.lean`,
`sheafification_preserves_finite_products`). Its general theorem is already
available in Lean 4 mathlib; here we establish its hypotheses for the explicit
closed reflection.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ToposPort.ClosedSubtopos

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable (P : C)

/-- A point over `P`, unique in every context over `P`, makes an object closed. -/
theorem closed_of_point_hom_ext {B : C} (s : P ⟶ B)
    (h : ∀ {Q : C} (_p : Q ⟶ P) (f g : Q ⟶ B), f = g) : IsClosed P B := by
  refine ⟨⟨prod.lift (𝟙 P) s, ?_, by simp⟩⟩
  apply prod.hom_ext
  · simp
  · apply h prod.fst

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- Closed objects form an exponential ideal. -/
theorem exponential_isClosed {B : C} (hB : IsClosed P B) (A : C) :
    IsClosed P ((ihom A).obj B) := by
  apply closed_of_point_hom_ext P
    (MonoidalClosed.curry (CartesianMonoidalCategory.snd A P ≫ point P hB))
  intro Q p f g
  apply MonoidalClosed.uncurry_injective
  apply closed_hom_ext P hB (CartesianMonoidalCategory.snd A Q ≫ p)

instance inclusion_exponentialIdeal : ExponentialIdeal (inclusion P) := by
  apply ExponentialIdeal.mk'
  intro B A
  exact ⟨⟨(ihom A).obj B.obj, exponential_isClosed P B.property A⟩, ⟨Iso.refl _⟩⟩

variable [HasPushouts C] (hP : IsSubterminal P)

/-- The explicit adjunction packaged as a reflective inclusion. -/
@[instance_reducible]
def reflective : Reflective (inclusion P) where
  L := reflector P hP
  adj := adjunction P hP

/-- The closed category has the finite products inherited by a reflection. -/
@[instance_reducible]
def closedCartesianMonoidalCategory : CartesianMonoidalCategory (ClosedObjects P) := by
  letI := reflective P hP
  exact CartesianMonoidalCategory.ofReflective (inclusion P)

/-- The closed category is itself cartesian closed. -/
@[instance_reducible]
def closedMonoidalClosed :
    letI := closedCartesianMonoidalCategory P hP
    MonoidalClosed (ClosedObjects P) := by
  letI := reflective P hP
  letI := closedCartesianMonoidalCategory P hP
  exact cartesianClosedOfReflective (inclusion P)

/-- The closed reflector preserves finite products. -/
theorem reflector_preservesFiniteProducts : PreservesFiniteProducts (reflector P hP) := by
  let := reflective P hP
  let := closedCartesianMonoidalCategory P hP
  let : BraidedCategory C := .ofCartesianMonoidalCategory
  exact PreservesFiniteProducts.of_exponentialIdeal (inclusion P)

include hP in
/-- The underlying closed-reflection endofunctor preserves finite products. -/
theorem functor_preservesFiniteProducts : PreservesFiniteProducts (functor P) := by
  let := reflective P hP
  let := reflector_preservesFiniteProducts P hP
  have h : PreservesFiniteProducts (reflector P hP ⋙ inclusion P) := inferInstance
  exact h

end ToposPort.ClosedSubtopos
