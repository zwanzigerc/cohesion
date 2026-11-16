import Cohesion.Continuity

/-! # Cohesive quadruples with the actual Continuity axiom

Continuity means that the canonical comparison constructed from evaluation is
an isomorphism. It is not an independently supplied comparison map. When the
ambient categories are elementary toposes, this is the cohesion axiom used in
the paper.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace Cohesion

universe v u₁ u₂
variable {E : Type u₁} {S : Type u₂} [Category.{v} E] [Category.{v} S]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory S]
  [MonoidalClosed E] [MonoidalClosed S]

namespace PrecohesiveMorphism

/-- Full Continuity for the canonical comparison defined by evaluation. -/
def Continuity (p : Cohesion.PrecohesiveMorphism E S) : Prop :=
  ∀ (X : E) (A : S), IsIso (continuityComparison p X A)

variable {p : Cohesion.PrecohesiveMorphism E S}

/-- Full Continuity implies epic Continuity. -/
theorem Continuity.epic (h : Continuity p) : EpicContinuity p := by
  intro X A
  have := h X A
  infer_instance

/-- Full Continuity implies monic Continuity. -/
theorem Continuity.monic (h : Continuity p) : MonicContinuity p := by
  intro X A
  have := h X A
  infer_instance

end PrecohesiveMorphism

/-- A pre-cohesive quadruple satisfying Continuity. The hypotheses that the
ambient categories are toposes are supplied separately when needed. -/
structure CohesiveMorphism (E : Type u₁) (S : Type u₂)
    [Category.{v} E] [Category.{v} S]
    [CartesianMonoidalCategory E] [CartesianMonoidalCategory S]
    [MonoidalClosed E] [MonoidalClosed S]
    extends Cohesion.PrecohesiveMorphism E S where
  continuity : PrecohesiveMorphism.Continuity toPrecohesiveMorphism

end Cohesion
