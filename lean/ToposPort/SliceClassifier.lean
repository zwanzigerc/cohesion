/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The slice construction accompanies the Lean 4 adaptation of Bhavik Mehta's
Lean 3 elementary-topos development. This proof uses the current mathlib
subobject-classifier and pullback APIs.
-/
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Subobject classifiers in slices

If `C` has pullbacks and a subobject classifier, every slice `Over B` has a
subobject classifier. Its truth arrow is `B → Ω × B`, with components truth
and the identity. No local-cartesian-closure assumption is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ToposPort

variable {C : Type u} [Category.{v} C]

namespace SliceClassifier

variable (c : Subobject.Classifier C) (B : C) [HasBinaryProducts C]

/-- The truth map in the slice over `B`, regarded in `C`. -/
def truthLeft : B ⟶ c.Ω ⨯ B :=
  prod.lift (c.χ₀ B ≫ c.truth) (𝟙 B)

/-- The truth square is a pullback of the original classifier. -/
lemma truth_isPullback :
    IsPullback (truthLeft c B) (c.χ₀ B) prod.fst c.truth := by
  refine IsPullback.of_isLimit' ⟨by simp [truthLeft]⟩ ?_
  refine PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ prod.snd) ?_ ?_ ?_
  · intro s
    apply prod.hom_ext
    · simp only [Category.assoc, truthLeft, prod.lift_fst]
      rw [s.condition, ← Category.assoc, ← Category.assoc]
      congr 1
      exact c.isTerminalΩ₀.hom_ext _ _
    · simp [truthLeft]
  · intro s
    exact c.isTerminalΩ₀.hom_ext _ _
  · intro s m hm _
    simpa [truthLeft] using congrArg (fun k => k ≫ prod.snd) hm

/-- The classifier object in the slice. -/
def omega : Over B := Over.mk (prod.snd : c.Ω ⨯ B ⟶ B)

/-- The truth arrow in the slice. -/
def truth : Over.mk (𝟙 B) ⟶ omega c B :=
  Over.homMk (truthLeft c B) (by simp [truthLeft, omega])

/-- The characteristic map in the slice is the ordinary characteristic map
paired with the structure map to the base. -/
def characteristic {U X : Over B} (m : U ⟶ X) [Mono m] : X ⟶ omega c B :=
  Over.homMk (prod.lift (c.χ m.left) X.hom) (by simp [omega])

lemma characteristic_isPullback {U X : Over B} (m : U ⟶ X) [Mono m] :
    IsPullback m (Over.mkIdTerminal.from U) (characteristic c B m) (truth c B) := by
  apply IsPullback.of_map_of_faithful (Over.forget B)
  simp only [Over.forget_map, Over.mkIdTerminal_from_left]
  change IsPullback m.left U.hom (prod.lift (c.χ m.left) X.hom) (truthLeft c B)
  have h : IsPullback m.left (U.hom ≫ c.χ₀ B)
      (prod.lift (c.χ m.left) X.hom ≫ prod.fst) c.truth := by
    simpa only [prod.lift_fst, c.isTerminalΩ₀.hom_ext (U.hom ≫ c.χ₀ B) (c.χ₀ U.left)]
      using c.isPullback m.left
  apply h.of_bot _ (truth_isPullback c B)
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, truthLeft]
    rw [(c.isPullback m.left).w, ← Category.assoc]
    congr 1
    exact c.isTerminalΩ₀.hom_ext _ _
  · simp [truthLeft]

set_option backward.isDefEq.respectTransparency false in
lemma characteristic_unique {U X : Over B} (m : U ⟶ X) [Mono m]
    (χ' : X ⟶ omega c B)
    (h : IsPullback m (Over.mkIdTerminal.from U) χ' (truth c B)) :
    χ' = characteristic c B m := by
  have h' := h.map (Over.forget B)
  have h'' := h'.paste_vert (truth_isPullback c B)
  have heq : χ'.left ≫ prod.fst = c.χ m.left := c.uniq m.left h''
  apply Over.OverMorphism.ext
  change χ'.left = prod.lift (c.χ m.left) X.hom
  apply prod.hom_ext
  · simpa using heq
  · simpa [omega] using Over.w χ'

/-- The explicit subobject classifier in `C/B`. -/
def classifier : Subobject.Classifier (Over B) :=
  Subobject.Classifier.mkOfTerminalΩ₀ _ Over.mkIdTerminal (omega c B)
    (truth c B) (characteristic c B) (characteristic_isPullback c B)
    (characteristic_unique c B)

end SliceClassifier

/-- Slices inherit subobject classifiers from a category with pullbacks. -/
theorem hasSubobjectClassifier_over [HasPullbacks C] [HasSubobjectClassifier C] (B : C) :
    HasSubobjectClassifier (Over B) := by
  let c : Subobject.Classifier C := HasSubobjectClassifier.exists_classifier.some
  let : HasTerminal C := c.isTerminalΩ₀.hasTerminal
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  exact ⟨⟨SliceClassifier.classifier c B⟩⟩

end ToposPort
