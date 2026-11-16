import Positive.Continuity
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Internally local sections from an epimorphism of powers

This is the categorical pullback-and-evaluation argument used in the positive
cohesion theorem. The hypothesis that epimorphisms are stable under pullback
is explicit, and is satisfied in an elementary topos.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace Positive

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C]

/-- A morphism has a section after an epimorphic cover of the terminal object.
The product is written with the target first, matching mathlib's currying
convention; symmetry gives the formulation `V × B → A` in the paper. -/
def HasInternallyLocalSection {A B : C} (f : A ⟶ B) : Prop :=
  ∃ (V : C) (v : V ⟶ 𝟙_ C), Epi v ∧
    ∃ s : B ⊗ V ⟶ A, s ≫ f = fst B V

/-- If exponentiating `f : A → B` by its target gives an epimorphism, then
`f` has an internally local section. -/
theorem internallyLocalSection_of_epi_power [HasPullbacks C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    {A B : C} (f : A ⟶ B) [Epi ((ihom B).map f)] :
    HasInternallyLocalSection f := by
  let idB : 𝟙_ C ⟶ (ihom B).obj B := curry (ρ_ B).hom
  let e := (ihom B).map f
  refine ⟨pullback e idB, pullback.snd e idB, ?_,
    uncurry (pullback.fst e idB), ?_⟩
  · exact (MorphismProperty.epimorphisms C).pullback_snd e idB inferInstance
  · rw [← uncurry_natural_right, pullback.condition, uncurry_natural_left]
    simp only [idB, uncurry_curry, fst_def]
    congr 2
    exact isTerminalTensorUnit.hom_ext _ _

section Precohesive

universe u₁ u₂
variable {E : Type u₁} {S : Type u₂} [Category.{v} E] [Category.{v} S]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory S]
  [MonoidalClosed E] [MonoidalClosed S] [HasPullbacks S]
  [(MorphismProperty.epimorphisms S).IsStableUnderBaseChange]

/-- Under epic Continuity, the canonical points-to-pieces map has an
internally local section. This is the local-sections lemma of the paper. -/
theorem local_sections (p : Cohesion.PrecohesiveMorphism E S)
    (h : PrecohesiveMorphism.EpicContinuity p) (X : E) :
    HasInternallyLocalSection ((PrecohesiveMorphism.theta p).app X) := by
  have := PrecohesiveMorphism.epi_theta_power p h X (p.pieces.obj X)
  exact internallyLocalSection_of_epi_power _

end Precohesive
end Positive
