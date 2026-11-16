/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

Lean 4 representation-based adaptation of the abstract power-object machinery
in b-mehta/topos/src/power.lean (c9032b11789e36038bc841a1e2b486972421b983).
Source adaptation: the Lean 4 port uses the 2026 mathlib API.
-/
import ToposPort.PowerObjects

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
namespace ToposPort.AbstractPower
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open Opposite
variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

/-- Power objects specified by their actual universal property. No cartesian
closure or preservation assumptions are part of this definition. -/
class HasPowerObjects where
  powerObject : C → C
  representation (A : C) :
    ((tensorLeft A).op ⋙ Subobject.presheaf C).RepresentableBy (powerObject A)

variable {C} [HasPowerObjects C]

abbrev powerObject (A : C) : C := HasPowerObjects.powerObject A

def powerHomEquiv (A B : C) : (B ⟶ powerObject A) ≃ Subobject (A ⊗ B) :=
  (HasPowerObjects.representation A).homEquiv

abbrev powerName {A B : C} (s : Subobject (A ⊗ B)) : B ⟶ powerObject A :=
  (powerHomEquiv A B).symm s

theorem powerHomEquiv_natural (A : C) {B B' : C} (f : B' ⟶ B)
    (g : B ⟶ powerObject A) :
    powerHomEquiv A B' (f ≫ g) =
      (Subobject.pullback (A ◁ f)).obj (powerHomEquiv A B g) :=
  (HasPowerObjects.representation A).homEquiv_comp f g

lemma powerName_natural {A B B' : C} (f : B' ⟶ B) (s : Subobject (A ⊗ B)) :
    powerName ((Subobject.pullback (A ◁ f)).obj s) = f ≫ powerName s := by
  apply (powerHomEquiv _ _).injective
  rw [Equiv.apply_symm_apply, powerHomEquiv_natural, Equiv.apply_symm_apply]

/-- Inverse image, represented by the universal relation. -/
def powerMap {A B : C} (f : A ⟶ B) : powerObject B ⟶ powerObject A :=
  powerName ((Subobject.pullback (f ▷ powerObject B)).obj (powerHomEquiv B _ (𝟙 _)))

lemma powerHomEquiv_pre {A B X : C} (f : A ⟶ B) (k : X ⟶ powerObject B) :
    powerHomEquiv A X (k ≫ powerMap f) =
      (Subobject.pullback (f ▷ X)).obj (powerHomEquiv B X k) := by
  rw [powerHomEquiv_natural, powerMap, Equiv.apply_symm_apply]
  have hk := powerHomEquiv_natural B k (𝟙 (powerObject B))
  simp only [Category.comp_id] at hk
  rw [hk, ← Subobject.pullback_comp, ← Subobject.pullback_comp]
  rw [whisker_exchange]

lemma powerName_pre {A B X : C} (f : A ⟶ B) (s : Subobject (B ⊗ X)) :
    powerName ((Subobject.pullback (f ▷ X)).obj s) = powerName s ≫ powerMap f := by
  apply (powerHomEquiv _ _).injective
  rw [Equiv.apply_symm_apply, powerHomEquiv_pre, Equiv.apply_symm_apply]

@[simp] lemma powerMap_id (A : C) : powerMap (𝟙 A) = 𝟙 (powerObject A) := by
  simp [powerMap, Subobject.pullback_id]

@[simp] lemma powerMap_comp {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
    powerMap (f ≫ g) = powerMap g ≫ powerMap f := by
  apply (powerHomEquiv _ _).injective
  rw [powerHomEquiv_pre, powerMap, powerMap, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, ← Subobject.pullback_comp, comp_whiskerRight]

def powerFunctor : Cᵒᵖ ⥤ C where
  obj A := powerObject A.unop
  map f := powerMap f.unop
  map_id A := powerMap_id A.unop
  map_comp f g := powerMap_comp g.unop f.unop

local instance : BraidedCategory C := .ofCartesianMonoidalCategory

/-- Transposing a relation swaps its two coordinates. -/
def powerTranspose (A B : C) : (A ⟶ powerObject B) ≃ (B ⟶ powerObject A) where
  toFun f := powerName ((Subobject.pullback (β_ A B).hom).obj (powerHomEquiv B A f))
  invFun f := powerName ((Subobject.pullback (β_ B A).hom).obj (powerHomEquiv A B f))
  left_inv f := by
    dsimp only [powerName]
    rw [Equiv.apply_symm_apply, ← Subobject.pullback_comp, SymmetricCategory.symmetry,
      Subobject.pullback_id]
    exact Equiv.symm_apply_apply _ _
  right_inv f := by
    dsimp only [powerName]
    rw [Equiv.apply_symm_apply, ← Subobject.pullback_comp, SymmetricCategory.symmetry,
      Subobject.pullback_id]
    exact Equiv.symm_apply_apply _ _

/-- The contravariant power-object functor is self-adjoint on the right. -/
def powerSelfAdjunction : (powerFunctor (C := C)).rightOp ⊣ powerFunctor :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun A B => (CategoryTheory.opEquiv _ _).trans (powerTranspose B.unop A)
    homEquiv_naturality_left_symm := by
      intro A A' B f g
      apply Quiver.Hom.unop_inj
      change powerName ((Subobject.pullback (β_ A B.unop).hom).obj
        (powerHomEquiv B.unop A (f ≫ g))) =
        powerName ((Subobject.pullback (β_ A' B.unop).hom).obj
          (powerHomEquiv B.unop A' g)) ≫ powerMap f
      rw [powerHomEquiv_natural, ← powerName_pre]
      congr 1
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp,
        BraidedCategory.braiding_naturality_left]
    homEquiv_naturality_right := by
      intro A B B' f g
      change powerName ((Subobject.pullback (β_ B'.unop A).hom).obj
        (powerHomEquiv A B'.unop (g.unop ≫ f.unop))) =
        powerName ((Subobject.pullback (β_ B.unop A).hom).obj
          (powerHomEquiv A B.unop f.unop)) ≫ powerMap g.unop
      rw [powerHomEquiv_natural, ← powerName_pre]
      congr 1
      rw [← Subobject.pullback_comp, ← Subobject.pullback_comp,
        BraidedCategory.braiding_naturality_left]
  }

instance powerFunctor_isRightAdjoint : (powerFunctor (C := C)).IsRightAdjoint :=
  ⟨_, ⟨powerSelfAdjunction⟩⟩

variable [HasSubobjectClassifier C]

/-- Inverse image on power objects distinguishes every pair of maps. -/
theorem power_map_injective {A B : C} {f g : A ⟶ B}
    (h : powerMap f = powerMap g) : f = g := by
  let δ : B ⟶ B ⊗ B := lift (𝟙 B) (𝟙 B)
  let c := HasSubobjectClassifier.χ δ
  have he : f ▷ B ≫ c = g ▷ B ≫ c := by
    apply HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv.injective
    rw [HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv_comp,
      HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv_comp]
    have hc' : HasSubobjectClassifier.exists_classifier.some.representableBy.homEquiv c =
        Subobject.mk δ := HasSubobjectClassifier.exists_classifier.some.pullback_χ_obj_mk_truth δ
    rw [hc']
    change (Subobject.pullback (f ▷ B)).obj (Subobject.mk δ) =
      (Subobject.pullback (g ▷ B)).obj (Subobject.mk δ)
    have hf := powerHomEquiv_pre f (powerName (Subobject.mk δ))
    have hg := powerHomEquiv_pre g (powerName (Subobject.mk δ))
    rw [Equiv.apply_symm_apply] at hf hg
    rw [← hf, ← hg, h]
  have hd : lift f f ≫ c = lift g f ≫ c := by
    have hh := congrArg (fun k => lift (𝟙 A) f ≫ k) he
    simpa only [← Category.assoc, lift_whiskerRight, Category.id_comp] using hh
  let q : Subobject.Classifier C := HasSubobjectClassifier.exists_classifier.some
  have hc : lift g f ≫ c = q.χ₀ A ≫ q.truth := by
    rw [← hd]
    calc
      lift f f ≫ c = f ≫ δ ≫ c := by
        rw [← Category.assoc]; congr 1; simp [δ, comp_lift]
      _ = f ≫ q.χ₀ B ≫ q.truth := by rw [HasSubobjectClassifier.comm]
      _ = q.χ₀ A ≫ q.truth := by
        rw [← Category.assoc]; congr 1; exact Subsingleton.elim _ _
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

/-- Cartesian closure and a classifier supply abstract power objects. -/
@[instance_reducible]
def hasPowerObjects_of_cartesianClosed [MonoidalClosed C] : HasPowerObjects C where
  powerObject := ToposPort.powerObject
  representation := ToposPort.powerRepresentation

end ToposPort.AbstractPower
