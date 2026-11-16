import Cohesion.Precohesive
import Counterexample.PresheafReflection
import Counterexample.ProductTransfer
import Counterexample.PullbackObstruction

/-!
# The pre-cohesive morphism from a split reflection

The categorical structure and local-connectedness condition are imported
from `Cohesion.Precohesive`; compatibility aliases preserve the earlier API.
Here the presheaf construction verifies every field of that shared structure.
Its finite-limit-preserving middle left adjoint is the inverse image of the
required geometric morphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Counterexample

universe v₁ v₂ u₁ u₂

-- Compatibility names for the shared cohesion API.
export Cohesion (PrecohesiveMorphism)

namespace PrecohesiveMorphism
export Cohesion.PrecohesiveMorphism
  (mk pieces discrete points codiscrete adjunctions discreteFullyFaithful
    codiscreteFullyFaithful discretePreservesFiniteLimits piecesPreservesFiniteProducts
    nullstellensatz LocallyConnected)
end PrecohesiveMorphism

section Presheaves

universe u
open Precohesion.PresheafReflection
variable {A B : Type u} [SmallCategory A] [SmallCategory B]

/-- The general presheaf construction, with every pre-cohesion axiom proved. -/
def precohesiveOfSplitReflection (a : B ⥤ A) (i : A ⥤ B) (adj : a ⊣ i)
    [i.Full] [i.Faithful] [HasFiniteProducts B] [PreservesFiniteProducts a]
    [∀ X, IsSplitEpi (adj.unit.app X)] : PrecohesiveMorphism (Psh B) (Psh A) where
  pieces := pieces a
  discrete := discrete a
  points := points i
  codiscrete := codiscrete i
  adjunctions := quadruple adj
  discreteFullyFaithful := discreteFullyFaithful adj
  codiscreteFullyFaithful := codiscreteFullyFaithful adj
  discretePreservesFiniteLimits := inferInstance
  piecesPreservesFiniteProducts := preservesFiniteProducts_lan_op a
  nullstellensatz := theta_epi_of_split_units adj

end Presheaves

end Counterexample
