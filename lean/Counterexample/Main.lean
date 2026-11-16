import Counterexample.IndexCategories
import Counterexample.Precohesive
import Counterexample.ContinuityWitness

/-!
# A pre-cohesive presheaf morphism which is not locally connected

This is the main counterexample. The indexing categories contain all group
homomorphisms between finite product expressions in `S₃`, `C₂`, and `C₃`.
Abelianization supplies a product-preserving reflection with split units.
The sign-kernel pullback supplies the obstruction to local connectedness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Precohesion.PresheafReflection

namespace Counterexample

/-- The explicit pre-cohesive morphism between the two presheaf categories. -/
def counterexample : PrecohesiveMorphism (Psh GroupWord) (Psh AbelianWord) :=
  precohesiveOfSplitReflection reflector inclusion reflection

/-- The counterexample fails the pullback characterization of local connectedness. -/
theorem counterexample_not_locallyConnected : ¬ counterexample.LocallyConnected := by
  change ¬ PresheafLocallyConnected reflector
  exact presheaf_not_locallyConnected reflector inclusion reflection unitToC2
    kernelInclusion kernelToUnit signMorphism kernelSquare_isPullback
    kernelSquare_not_preserved

/-- In particular, pre-cohesion does not imply local connectedness. -/
theorem exists_precohesive_not_locallyConnected :
    ∃ p : PrecohesiveMorphism (Psh GroupWord) (Psh AbelianWord),
      ¬ p.LocallyConnected :=
  ⟨counterexample, counterexample_not_locallyConnected⟩

/-- Both negative assertions in the paper's counterexample theorem, for the
explicit pre-cohesive morphism constructed above. -/
theorem counterexample_specification :
    ¬ counterexample.LocallyConnected ∧
      ¬ Mono (continuityComparison reflection (yoneda.obj GroupWord.s3)
        (yoneda.obj AbelianWord.c3)) :=
  ⟨counterexample_not_locallyConnected, canonical_continuity_not_mono⟩

end Counterexample
