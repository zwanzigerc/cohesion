/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

Adapted to Lean 4 and current mathlib's internal-hom and classifier APIs in 2026.
Source: b-mehta/topos, src/power.lean, commit
c9032b11789e36038bc841a1e2b486972421b983.
Source adaptation: the Lean 4 port uses the 2026 mathlib API.
-/
import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Power objects in an elementary topos

The exponential Ω^A represents subobjects of A × B, naturally in B.
The induced contravariant power-object functor is self-adjoint on the right.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

namespace ToposPort

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open Opposite

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [MonoidalClosed C] [HasSubobjectClassifier C]

/-- The power object Ω^A. -/
abbrev powerObject (A : C) : C := A ⟶[C] HasSubobjectClassifier.Ω C

/-- Contravariant inverse image on power objects. -/
abbrev powerFunctor : Cᵒᵖ ⥤ C :=
  MonoidalClosed.internalHom.flip.obj (HasSubobjectClassifier.Ω C)

/-- The exponential/classifier equivalence, in the tensor-product convention of mathlib. -/
def powerHomEquiv [HasPullbacks C] (A B : C) :
    (B ⟶ powerObject A) ≃ Subobject (A ⊗ B) :=
  ((ihom.adjunction A).homEquiv _ _).symm.trans
    HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv

/-- This equivalence is natural under change of the parameter object. -/
theorem powerHomEquiv_natural [HasPullbacks C] (A : C) {B B' : C}
    (f : B' ⟶ B) (g : B ⟶ powerObject A) :
    powerHomEquiv A B' (f ≫ g) =
      (Subobject.pullback (A ◁ f)).obj (powerHomEquiv A B g) := by
  change HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv
    (uncurry (f ≫ g)) = _
  rw [MonoidalClosed.uncurry_natural_left]
  exact HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv_comp _ _

local instance : BraidedCategory C := .ofCartesianMonoidalCategory

/-- Transposition of a relation, as an equivalence between two exponential hom sets. -/
def powerTranspose (A B : C) : (A ⟶ powerObject B) ≃ (B ⟶ powerObject A) where
  toFun f := curry ((β_ A B).hom ≫ uncurry f)
  invFun f := curry ((β_ B A).hom ≫ uncurry f)
  left_inv f := by simp only [uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]
  right_inv f := by simp only [uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp, curry_uncurry]

/-- The contravariant power-object functor is self-adjoint on the right. -/
def powerSelfAdjunction : (powerFunctor (C := C)).rightOp ⊣ powerFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun A B => (CategoryTheory.opEquiv _ _).trans (powerTranspose B.unop A)
    homEquiv_naturality_left_symm := by
      intro A A' B f g
      apply Quiver.Hom.unop_inj
      apply uncurry_injective
      change uncurry (curry ((β_ A B.unop).hom ≫ uncurry (f ≫ g))) =
        uncurry (curry ((β_ A' B.unop).hom ≫ uncurry g) ≫
          (MonoidalClosed.pre f).app (HasSubobjectClassifier.Ω C))
      rw [MonoidalClosed.uncurry_pre_app, uncurry_curry, uncurry_curry, uncurry_natural_left]
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]
    homEquiv_naturality_right := by
      intro A B B' f g
      apply uncurry_injective
      change uncurry (curry ((β_ B'.unop A).hom ≫ uncurry (g.unop ≫ f.unop))) =
        uncurry (curry ((β_ B.unop A).hom ≫ uncurry f.unop) ≫
          (MonoidalClosed.pre g.unop).app (HasSubobjectClassifier.Ω C))
      rw [MonoidalClosed.uncurry_pre_app, uncurry_curry, uncurry_curry, uncurry_natural_left]
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left, Category.assoc]
  }

/-- Exponentiation into Ω represents the presheaf of subobjects of A × (-). -/
def powerRepresentation [HasPullbacks C] (A : C) :
    ((tensorLeft A).op ⋙ Subobject.presheaf C).RepresentableBy (powerObject A) where
  homEquiv := powerHomEquiv A _
  homEquiv_comp := powerHomEquiv_natural A

/-- The inverse-image operation on power objects distinguishes all morphisms. -/
theorem power_map_injective {A B : C} {f g : A ⟶ B}
    (h : (pre f).app (HasSubobjectClassifier.Ω C) =
      (pre g).app (HasSubobjectClassifier.Ω C)) : f = g := by
  let δ : B ⟶ B ⊗ B := lift (𝟙 B) (𝟙 B)
  let c := HasSubobjectClassifier.χ δ
  have he : f ▷ B ≫ c = g ▷ B ≫ c := by
    have hh := congrArg (fun k => uncurry (curry c ≫ k)) h
    simpa only [uncurry_pre_app, uncurry_curry] using hh
  have hd : lift f f ≫ c = lift g f ≫ c := by
    have hh := congrArg (fun k => lift (𝟙 A) f ≫ k) he
    simpa only [← Category.assoc, lift_whiskerRight, Category.id_comp] using hh
  let q : Subobject.Classifier C := HasSubobjectClassifier.exists_classifier.some
  have hc : lift g f ≫ c = q.χ₀ A ≫ q.truth := by
    rw [← hd]
    calc
      lift f f ≫ c = f ≫ δ ≫ c := by rw [← Category.assoc]; congr 1; simp [δ, comp_lift]
      _ = f ≫ q.χ₀ B ≫ q.truth := by rw [HasSubobjectClassifier.comm]
      _ = q.χ₀ A ≫ q.truth := by rw [← Category.assoc]; congr 1; exact Subsingleton.elim _ _
  let k := (HasSubobjectClassifier.isPullback_χ δ).lift (lift g f) (q.χ₀ A) hc
  have hk : k ≫ δ = lift g f := IsPullback.lift_fst _ _ _ _
  have hkg : k = g := by
    simpa [δ] using congrArg (fun t => t ≫ fst B B) hk
  have hkf : k = f := by
    simpa [δ] using congrArg (fun t => t ≫ snd B B) hk
  exact hkf.symm.trans hkg

instance powerFunctor_faithful : (powerFunctor (C := C)).Faithful where
  map_injective h := Quiver.Hom.unop_inj (power_map_injective h)

instance powerFunctor_reflectsIsomorphisms :
    (powerFunctor (C := C)).ReflectsIsomorphisms := inferInstance

instance powerFunctor_isRightAdjoint : (powerFunctor (C := C)).IsRightAdjoint :=
  ⟨_, ⟨powerSelfAdjunction⟩⟩

end ToposPort
