import Positive.Continuity

/-! # Composition laws for canonical exponential comparisons -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory

namespace Positive
universe v u₁ u₂ u₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [CartesianMonoidalCategory C] [CartesianMonoidalCategory D] [CartesianMonoidalCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  (F : C ⥤ D) (G : D ⥤ E)
  [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]
  [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) G]

/-- Canonical exponential comparison respects composition of functors. -/
theorem expComparison_comp (A X : C) :
    (expComparison (F ⋙ G) A).natTrans.app X =
      G.map ((expComparison F A).natTrans.app X) ≫
        (expComparison G (F.obj A)).natTrans.app (F.obj X) := by
  apply MonoidalClosed.uncurry_injective
  rw [uncurry_expComparison, uncurry_natural_left, uncurry_expComparison]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  rw [← prodComparison_inv_natural_whiskerLeft_assoc, ← G.map_comp, expComparison_ev]
  rw [G.map_comp]
  simp only [prodComparison_comp, IsIso.inv_comp, G.map_inv, Category.assoc]

omit [CartesianMonoidalCategory E] [MonoidalClosed E] in
/-- Exponential comparison is natural in its exponent. -/
theorem expComparison_pre {A B : C} (f : B ⟶ A) (X : C) :
    F.map ((MonoidalClosed.pre f).app X) ≫ (expComparison F B).natTrans.app X =
      (expComparison F A).natTrans.app X ≫
        (MonoidalClosed.pre (F.map f)).app (F.obj X) := by
  have h := congrArg (fun t => t.natTrans.app X) (expComparison_whiskerLeft F f)
  exact h.symm

end Positive
