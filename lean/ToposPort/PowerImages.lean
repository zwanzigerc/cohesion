/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

Lean 4 adaptation of the internal-image and Beck–Chevalley arguments in
b-mehta/topos/src/power.lean (c9032b11789e36038bc841a1e2b486972421b983).
Source adaptation: the Lean 4 port uses the 2026 mathlib API.
-/
import ToposPort.PowerObjects
import Mathlib.CategoryTheory.Limits.Connected

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
namespace ToposPort
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasSubobjectClassifier C] [HasPullbacks C]
local instance : BraidedCategory C := .ofCartesianMonoidalCategory

local instance mono_whiskerRight {A B : C} (f : A ⟶ B) [Mono f] (X : C) :
    Mono (f ▷ X) := inferInstanceAs (Mono ((tensorRight X).map f))

/-- Naming a family of subobjects. -/
abbrev powerName {A B : C} (s : Subobject (A ⊗ B)) : B ⟶ powerObject A :=
  (powerHomEquiv A B).symm s

lemma powerName_natural {A B B' : C} (f : B' ⟶ B) (s : Subobject (A ⊗ B)) :
    powerName ((Subobject.pullback (A ◁ f)).obj s) = f ≫ powerName s := by
  apply (powerHomEquiv _ _).injective
  rw [Equiv.apply_symm_apply, powerHomEquiv_natural, Equiv.apply_symm_apply]

lemma powerHomEquiv_pre {A B X : C} (f : A ⟶ B) (k : X ⟶ powerObject B) :
    powerHomEquiv A X (k ≫ (pre f).app (HasSubobjectClassifier.Ω C)) =
      (Subobject.pullback (f ▷ X)).obj (powerHomEquiv B X k) := by
  change HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv
    (uncurry (k ≫ (pre f).app (HasSubobjectClassifier.Ω C))) = _
  rw [uncurry_pre_app]
  exact HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv_comp _ _

lemma powerName_pre {A B X : C} (f : A ⟶ B) (s : Subobject (B ⊗ X)) :
    powerName ((Subobject.pullback (f ▷ X)).obj s) =
      powerName s ≫ (pre f).app (HasSubobjectClassifier.Ω C) := by
  apply (powerHomEquiv _ _).injective
  rw [Equiv.apply_symm_apply, powerHomEquiv_pre, Equiv.apply_symm_apply]

omit [MonoidalClosed C] [HasSubobjectClassifier C] [HasPullbacks C] in
/-- The square formed by changing the two independent product coordinates is a pullback. -/
lemma tensor_exchange_isPullback {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) :
    IsPullback (A ◁ g) (f ▷ X) (f ▷ Y) (B ◁ g) := by
  refine ⟨⟨(whisker_exchange f g)⟩, ⟨?_⟩⟩
  refine PullbackCone.IsLimit.mk _
    (fun s => lift (s.fst ≫ fst _ _) (s.snd ≫ snd _ _)) ?_ ?_ ?_
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · have h := congrArg (fun t => t ≫ snd B Y) s.condition
      simpa using h.symm
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · have h := congrArg (fun t => t ≫ fst B Y) s.condition
      simpa using h
    · simp
  · intro s m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · simpa using congrArg (fun t => t ≫ fst A Y) hm
    · simpa using congrArg (fun t => t ≫ snd B X) hn

omit [MonoidalClosed C] [HasSubobjectClassifier C] [HasPullbacks C] in
/-- Tensoring a pullback with a fixed object preserves the pullback. -/
lemma isPullback_whiskerRight {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y}
    {h : X ⟶ Z} {k : Y ⟶ Z} (sq : IsPullback f g h k) (T : C) :
    IsPullback (f ▷ T) (g ▷ T) (h ▷ T) (k ▷ T) := by
  have comm : (f ▷ T) ≫ (h ▷ T) = (g ▷ T) ≫ (k ▷ T) := by
    simp only [← comp_whiskerRight, sq.w]
  refine ⟨⟨comm⟩, ⟨?_⟩⟩
  refine PullbackCone.IsLimit.mk _
    (fun s => lift (sq.lift (s.fst ≫ fst _ _) (s.snd ≫ fst _ _) (by
      simpa using congrArg (fun t => t ≫ fst Z T) s.condition))
      (s.fst ≫ snd _ _)) ?_ ?_ ?_
  · intro s
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using congrArg (fun t => t ≫ snd Z T) s.condition
  · intro s m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · apply sq.hom_ext
      · simpa using congrArg (fun t => t ≫ fst X T) hm
      · simpa using congrArg (fun t => t ≫ fst Y T) hn
    · simpa using congrArg (fun t => t ≫ snd X T) hm

/-- Direct image on power objects, for a monomorphism. -/
def powerImage {A B : C} (f : A ⟶ B) [Mono f] : powerObject A ⟶ powerObject B :=
  powerName ((Subobject.map (f ▷ powerObject A)).obj (powerHomEquiv A _ (𝟙 _)))

lemma powerImage_natural {A B X : C} (f : A ⟶ B) [Mono f]
    (k : X ⟶ powerObject A) :
    k ≫ powerImage f =
      powerName ((Subobject.map (f ▷ X)).obj (powerHomEquiv A X k)) := by
  rw [powerImage, ← powerName_natural]
  congr 1
  rw [← Subobject.map_pullback (tensor_exchange_isPullback f k).w
    (tensor_exchange_isPullback f k).isLimit]
  rw [← powerHomEquiv_natural, Category.comp_id]

/-- Image followed by inverse image along a mono is the identity. -/
lemma powerImage_pre {A B : C} (f : A ⟶ B) [Mono f] :
    powerImage f ≫ (pre f).app (HasSubobjectClassifier.Ω C) = 𝟙 _ := by
  rw [powerImage, ← powerName_pre, Subobject.pullback_map_self]
  exact Equiv.symm_apply_apply _ _

/-- Beck–Chevalley for direct images along monomorphisms. -/
theorem powerImage_beckChevalley {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y}
    {h : X ⟶ Z} {k : Y ⟶ Z} [Mono g] [Mono h] (sq : IsPullback f g h k) :
    powerImage h ≫ (pre k).app (HasSubobjectClassifier.Ω C) =
      (pre f).app (HasSubobjectClassifier.Ω C) ≫ powerImage g := by
  rw [powerImage, ← powerName_pre, powerImage_natural]
  have hh := powerHomEquiv_pre f (𝟙 (powerObject X))
  simp only [Category.id_comp] at hh
  rw [hh]
  rw [← Subobject.map_pullback (isPullback_whiskerRight sq _).w
    (isPullback_whiskerRight sq _).isLimit]

end ToposPort
