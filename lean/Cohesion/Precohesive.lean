import Cohesion.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Quadruple
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Pre-cohesive adjoint quadruples

The shared categorical assumptions of the paper. The Nullstellensatz uses
mathlib's canonical points-to-pieces map for the adjoint triple.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Cohesion

universe v₁ v₂ u₁ u₂

/-- The four adjoints and the pre-cohesion adjoint conditions used in the paper.
It applies to both the positive theorem and the presheaf counterexample. -/
structure PrecohesiveMorphism (E : Type u₁) (S : Type u₂)
    [Category.{v₁} E] [Category.{v₂} S] where
  pieces : E ⥤ S
  discrete : S ⥤ E
  points : E ⥤ S
  codiscrete : S ⥤ E
  adjunctions : Adjunction.Quadruple pieces discrete points codiscrete
  discreteFullyFaithful : discrete.FullyFaithful
  codiscreteFullyFaithful : codiscrete.FullyFaithful
  discretePreservesFiniteLimits : PreservesFiniteLimits discrete
  piecesPreservesFiniteProducts : PreservesFiniteProducts pieces
  nullstellensatz :
    letI : discrete.Full := discreteFullyFaithful.full
    letI : discrete.Faithful := discreteFullyFaithful.faithful
    ∀ X : E, Epi (adjunctions.leftTriple.rightToLeft.app X)

/-- Local connectedness, in the pullback characterization of the paper. -/
def PrecohesiveMorphism.LocallyConnected
    {E : Type u₁} {S : Type u₂} [Category.{v₁} E] [Category.{v₂} S]
    (p : PrecohesiveMorphism E S) : Prop :=
  PreservesPullbacksAlong p.pieces p.discrete

end Cohesion
