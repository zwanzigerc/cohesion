/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Doubling a regular subobject

The pushout of a regular monomorphism along itself is a pullback. This direct
argument supplies the doubled-vertex construction without assuming adhesivity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ToposPort

variable {C : Type u} [Category.{v} C]

/-- Both inclusions in a double pushout are split monomorphisms, with the fold
map as a common retraction. -/
theorem doublePushout_isSplitMono_left {Q A P : C} {m : Q ⟶ A} {l r : A ⟶ P}
    (sq : IsPushout m m l r) : IsSplitMono l :=
  IsSplitMono.mk' ⟨sq.desc (𝟙 A) (𝟙 A) rfl, by simp⟩

theorem doublePushout_isSplitMono_right {Q A P : C} {m : Q ⟶ A} {l r : A ⟶ P}
    (sq : IsPushout m m l r) : IsSplitMono r :=
  doublePushout_isSplitMono_left sq.flip

/-- The pushout of a regular monomorphism along itself is a pullback. -/
theorem doublePushout_isPullback {Q A P : C} (m : Q ⟶ A) [IsRegularMono m]
    {l r : A ⟶ P} (sq : IsPushout m m l r) : IsPullback m m l r := by
  let fold := sq.desc (𝟙 A) (𝟙 A) rfl
  let test := sq.desc (IsRegularMono.left m) (IsRegularMono.right m) (IsRegularMono.w m)
  have same (s : PullbackCone l r) : s.fst = s.snd := by
    have h := congrArg (fun k => k ≫ fold) s.condition
    simpa [fold, Category.assoc] using h
  have equalizes (s : PullbackCone l r) :
      s.fst ≫ IsRegularMono.left m = s.fst ≫ IsRegularMono.right m := by
    have h := congrArg (fun k => k ≫ test) s.condition
    simpa [test, Category.assoc, same s] using h
  apply IsPullback.of_isLimit (c := PullbackCone.mk m m sq.w)
  refine PullbackCone.IsLimit.mk _
    (fun s => IsRegularMono.lift m s.fst (equalizes s)) ?_ ?_ ?_
  · intro s
    exact IsRegularMono.fac m _ _
  · intro s
    exact (IsRegularMono.fac m _ _).trans (same s)
  · intro s k hk _
    exact IsRegularMono.uniq m s.fst (equalizes s) k hk

/-- In a category with a subobject classifier, every double pushout of a
monomorphism is a pullback. No cartesian closure is required. -/
theorem doublePushout_isPullback_of_classifier [HasSubobjectClassifier C]
    {Q A P : C} (m : Q ⟶ A) [Mono m] {l r : A ⟶ P}
    (sq : IsPushout m m l r) : IsPullback m m l r := by
  let := IsRegularMonoCategory.regularMonoOfMono m
  exact doublePushout_isPullback m sq

end ToposPort
