import Cohesion.Continuity

/-! # Quality types

A pre-cohesive morphism is a quality type when its canonical comparison
from points to pieces is invertible.
-/

open CategoryTheory

namespace Cohesion.PrecohesiveMorphism

universe v u₁ u₂
variable {E : Type u₁} {S : Type u₂} [Category.{v} E] [Category.{v} S]

/-- A quality type has invertible canonical points-to-pieces comparison. -/
def IsQualityType (p : Cohesion.PrecohesiveMorphism E S) : Prop := IsIso (theta p)

/-- Quality is equivalently invertibility at every object. -/
theorem isQualityType_iff (p : Cohesion.PrecohesiveMorphism E S) :
    IsQualityType p ↔ ∀ X : E, IsIso ((theta p).app X) := by
  constructor
  · intro h X
    let : IsIso (theta p) := h
    infer_instance
  · intro h
    let (X : E) : IsIso ((theta p).app X) := h X
    exact NatIso.isIso_of_isIso_app _

end Cohesion.PrecohesiveMorphism
