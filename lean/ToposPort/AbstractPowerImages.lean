/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

Lean 4 adaptation of the internal-image and Beck–Chevalley arguments in
b-mehta/topos/src/power.lean (c9032b11789e36038bc841a1e2b486972421b983).
Source adaptation: the Lean 4 port uses the 2026 mathlib API.
-/
import ToposPort.AbstractPower
import ToposPort.PowerImages

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
namespace ToposPort.AbstractPower
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [HasPullbacks C] [HasPowerObjects C]
local instance : BraidedCategory C := .ofCartesianMonoidalCategory

local instance mono_whiskerRight {A B : C} (f : A ⟶ B) [Mono f] (X : C) :
    Mono (f ▷ X) := inferInstanceAs (Mono ((tensorRight X).map f))

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
    powerImage f ≫ powerMap f = 𝟙 _ := by
  rw [powerImage, ← powerName_pre, Subobject.pullback_map_self]
  exact Equiv.symm_apply_apply _ _

/-- Beck–Chevalley for direct images along monomorphisms. -/
theorem powerImage_beckChevalley {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y}
    {h : X ⟶ Z} {k : Y ⟶ Z} [Mono g] [Mono h] (sq : IsPullback f g h k) :
    powerImage h ≫ powerMap k =
      powerMap f ≫ powerImage g := by
  rw [powerImage, ← powerName_pre, powerImage_natural]
  have hh := powerHomEquiv_pre f (𝟙 (powerObject X))
  simp only [Category.id_comp] at hh
  rw [hh]
  rw [← Subobject.map_pullback (isPullback_whiskerRight sq _).w
    (isPullback_whiskerRight sq _).isLimit]

end ToposPort.AbstractPower
