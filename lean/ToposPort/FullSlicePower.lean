/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This equalizer construction follows the slice-power-object construction in
Bhavik Mehta's Lean 3 `topos/src/power.lean`, expressed using the modern
subobject lattice and representability APIs.
Source adaptation: the Lean 4 port uses the 2026 mathlib API.
Upstream power-object development: Copyright (c) 2020 Bhavik Mehta.
-/
import ToposPort.AbstractPower
import ToposPort.SubobjectOver
import ToposPort.SliceClosed
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Bounded families of subobjects

The first stage of the general slice-power-object construction: families of
subobjects lying inside a specified relation are represented by an equalizer
inside `B × P(A)`. All statements in this file are proved from elementary-topos
primitives.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u
namespace ToposPort
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [HasPullbacks C] [AbstractPower.HasPowerObjects C] [HasEqualizers C]

namespace BoundedPower

variable {A B : C} (R : Subobject (A ⊗ B))

/-- Restrict the universal family to the chosen relation over `B`. -/
def intersectRelation : B ⊗ AbstractPower.powerObject A ⟶ AbstractPower.powerObject A :=
  AbstractPower.powerName
    ((AbstractPower.powerHomEquiv A _ (snd B (AbstractPower.powerObject A))) ⊓
      (Subobject.pullback (A ◁ fst B (AbstractPower.powerObject A))).obj R)

/-- The object of subobjects lying inside the fibers of `R`. -/
def obj : Over B :=
  Over.mk (equalizer.ι (intersectRelation R) (snd B (AbstractPower.powerObject A)) ≫ fst B (AbstractPower.powerObject A))

/-- The underlying subobject named by a map into the bounded power object. -/
def name {T : Over B} (f : T ⟶ obj R) : T.left ⟶ AbstractPower.powerObject A :=
  f.left ≫ equalizer.ι (intersectRelation R) (snd B (AbstractPower.powerObject A)) ≫
    snd B (AbstractPower.powerObject A)

omit [HasEqualizers C] in
lemma intersect_natural {T : C} (t : T ⟶ B) (k : T ⟶ AbstractPower.powerObject A) :
    AbstractPower.powerHomEquiv A T (lift t k ≫ intersectRelation R) =
      AbstractPower.powerHomEquiv A T k ⊓ (Subobject.pullback (A ◁ t)).obj R := by
  rw [intersectRelation, ← AbstractPower.powerName_natural, Equiv.apply_symm_apply,
    Subobject.inf_pullback, ← AbstractPower.powerHomEquiv_natural]
  simp only [lift_snd, ← Subobject.pullback_comp, ← whiskerLeft_comp, lift_fst]

lemma name_le {T : Over B} (f : T ⟶ obj R) :
    AbstractPower.powerHomEquiv A T.left (name R f) ≤ (Subobject.pullback (A ◁ T.hom)).obj R := by
  have e : lift T.hom (name R f) =
      f.left ≫ equalizer.ι (intersectRelation R) (snd B (AbstractPower.powerObject A)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa [obj] using (Over.w f).symm
    · simp [name]
  have h : lift T.hom (name R f) ≫ intersectRelation R = name R f := by
    rw [e, Category.assoc, equalizer.condition]
    rfl
  have hh := intersect_natural R T.hom (name R f)
  rw [h] at hh
  exact inf_eq_left.mp hh.symm

/-- Naming a subobject contained in a fiber gives a map into the equalizer. -/
def fromSubobject {T : Over B} (s : Subobject (A ⊗ T.left))
    (hs : s ≤ (Subobject.pullback (A ◁ T.hom)).obj R) : T ⟶ obj R :=
  Over.homMk
    (equalizer.lift (lift T.hom (AbstractPower.powerName s)) (by
      apply (AbstractPower.powerHomEquiv A T.left).injective
      rw [intersect_natural, Equiv.apply_symm_apply, lift_snd, Equiv.apply_symm_apply,
        inf_eq_left.mpr hs])) (by simp [obj])

@[simp]
lemma name_fromSubobject {T : Over B} (s : Subobject (A ⊗ T.left))
    (hs : s ≤ (Subobject.pullback (A ◁ T.hom)).obj R) :
    name R (fromSubobject R s hs) = AbstractPower.powerName s := by
  simp [name, fromSubobject]

@[simp]
lemma fromSubobject_name {T : Over B} (f : T ⟶ obj R) :
    fromSubobject R (AbstractPower.powerHomEquiv A T.left (name R f)) (name_le R f) = f := by
  apply Over.OverMorphism.ext
  apply equalizer.hom_ext
  simp only [fromSubobject, Over.homMk_left, equalizer.lift_ι, Equiv.symm_apply_apply]
  apply CartesianMonoidalCategory.hom_ext
  · simpa [obj] using (Over.w f).symm
  · simp [name]

/-- The equalizer represents families of subobjects bounded by `R`. -/
def homEquiv (T : Over B) :
    (T ⟶ obj R) ≃ {s : Subobject (A ⊗ T.left) //
      s ≤ (Subobject.pullback (A ◁ T.hom)).obj R} where
  toFun f := ⟨AbstractPower.powerHomEquiv A T.left (name R f), name_le R f⟩
  invFun s := fromSubobject R s.1 s.2
  left_inv := fromSubobject_name R
  right_inv s := by apply Subtype.ext; simp

/-- Naturality of the representing correspondence on its underlying subobject. -/
lemma homEquiv_natural {T T' : Over B} (f : T' ⟶ T) (k : T ⟶ obj R) :
    (homEquiv R T' (f ≫ k)).1 =
      (Subobject.pullback (A ◁ f.left)).obj (homEquiv R T k).1 := by
  change AbstractPower.powerHomEquiv A T'.left (name R (f ≫ k)) = _
  rw [show name R (f ≫ k) = f.left ≫ name R k by simp [name]]
  exact AbstractPower.powerHomEquiv_natural A f.left (name R k)

end BoundedPower

omit [AbstractPower.HasPowerObjects C] [HasEqualizers C] in
/-- Subobjects of a mono's domain correspond to subobjects below that mono. -/
def subobjectMonoEquiv {X Y : C} (m : X ⟶ Y) [Mono m] :
    Subobject X ≃ {s : Subobject Y // s ≤ Subobject.mk m} where
  toFun s := ⟨(Subobject.map m).obj s, by
    rw [← Subobject.map_top m]
    exact (Subobject.map m).monotone le_top⟩
  invFun s := (Subobject.pullback m).obj s.1
  left_inv := Subobject.pullback_map_self m
  right_inv s := by
    apply Subtype.ext
    change (Subobject.map m).obj ((Subobject.pullback m).obj s.1) = s.1
    exact (Subobject.inf_eq_map_pullback' (MonoOver.mk m) s.1).symm.trans
      (inf_eq_right.mpr s.2)

namespace SlicePower

variable {B : C} (A : Over B)
attribute [local instance] Over.cartesianMonoidalCategory

/-- The graph of a slice object's structure map. -/
def graph : A.left ⟶ A.left ⊗ B := lift (𝟙 A.left) A.hom

instance graph_mono : Mono (graph A) := by
  have h : graph A ≫ fst A.left B = 𝟙 A.left := by simp [graph]
  exact mono_of_mono_fac h

/-- The inclusion of the slice product in the ordinary product. -/
def productInclusion (T : Over B) : (A ⊗ T).left ⟶ A.left ⊗ T.left :=
  lift (pullback.fst A.hom T.hom) (pullback.snd A.hom T.hom)

omit [AbstractPower.HasPowerObjects C] [HasEqualizers C] in
/-- Slice products are the fibers of the graph relation. -/
lemma graph_isPullback (T : Over B) :
    IsPullback (pullback.fst A.hom T.hom) (productInclusion A T)
      (graph A) (A.left ◁ T.hom) := by
  refine IsPullback.of_isLimit' ⟨?_⟩ ?_
  · apply CartesianMonoidalCategory.hom_ext
    · simp [graph, productInclusion]
    · simpa [graph, productInclusion] using pullback.condition (f := A.hom) (g := T.hom)
  · refine PullbackCone.IsLimit.mk _
      (fun s => pullback.lift s.fst (s.snd ≫ snd A.left T.left) (by
        simpa [graph] using congrArg (fun k => k ≫ snd A.left B) s.condition)) ?_ ?_ ?_
    · intro s; simp
    · intro s
      apply CartesianMonoidalCategory.hom_ext
      · simpa [graph, productInclusion] using
          congrArg (fun k => k ≫ fst A.left B) s.condition
      · simp [productInclusion]
    · intro s m hm hn
      apply pullback.hom_ext
      · simpa using hm
      · simpa [productInclusion] using congrArg (fun k => k ≫ snd A.left T.left) hn

instance productInclusion_mono (T : Over B) : Mono (productInclusion A T) :=
  (graph_isPullback A T).mono_snd_of_mono

omit [AbstractPower.HasPowerObjects C] [HasEqualizers C] in
lemma graph_pullback (T : Over B) :
    (Subobject.pullback (A.left ◁ T.hom)).obj (Subobject.mk (graph A)) =
      Subobject.mk (productInclusion A T) :=
  Subobject.pullback_obj_mk (graph_isPullback A T)

/-- The underlying object of the slice power object. -/
def obj : Over B := BoundedPower.obj (Subobject.mk (graph A))

/-- Maps to the candidate slice power object classify underlying subobjects
of slice products. -/
def underlyingHomEquiv (T : Over B) :
    (T ⟶ obj A) ≃ Subobject (A ⊗ T).left :=
  (BoundedPower.homEquiv (Subobject.mk (graph A)) T).trans
    ((Equiv.subtypeEquivRight (fun s => by rw [graph_pullback A T])).trans
      (subobjectMonoEquiv (productInclusion A T)).symm)

omit [AbstractPower.HasPowerObjects C] [HasEqualizers C] in
/-- Compatibility of the slice-product inclusion with reindexing. -/
lemma productInclusion_natural {T T' : Over B} (f : T' ⟶ T) :
    (A ◁ f).left ≫ productInclusion A T =
      productInclusion A T' ≫ (A.left ◁ f.left) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [productInclusion]

/-- The underlying classification equivalence is natural in the parameter object. -/
lemma underlyingHomEquiv_natural {T T' : Over B} (f : T' ⟶ T) (k : T ⟶ obj A) :
    underlyingHomEquiv A T' (f ≫ k) =
      (Subobject.pullback (A ◁ f).left).obj (underlyingHomEquiv A T k) := by
  change (Subobject.pullback (productInclusion A T')).obj
      (BoundedPower.homEquiv (Subobject.mk (graph A)) T' (f ≫ k)).1 =
    (Subobject.pullback (A ◁ f).left).obj
      ((Subobject.pullback (productInclusion A T)).obj
        (BoundedPower.homEquiv (Subobject.mk (graph A)) T k).1)
  rw [BoundedPower.homEquiv_natural, ← Subobject.pullback_comp,
    ← Subobject.pullback_comp, productInclusion_natural]

/-- The full classification equivalence in the slice category. -/
def homEquiv (T : Over B) : (T ⟶ obj A) ≃ Subobject (A ⊗ T) :=
  (underlyingHomEquiv A T).trans (subobjectOverEquiv (A ⊗ T)).symm.toEquiv

/-- Naturality in the slice parameter. -/
lemma homEquiv_natural {T T' : Over B} (f : T' ⟶ T) (k : T ⟶ obj A) :
    homEquiv A T' (f ≫ k) = (Subobject.pullback (A ◁ f)).obj (homEquiv A T k) := by
  apply (subobjectOverEquiv (A ⊗ T')).injective
  rw [subobjectOverEquiv_pullback]
  dsimp only [homEquiv, Equiv.trans_apply, OrderIso.coe_toEquiv]
  rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
  exact underlyingHomEquiv_natural A f k

/-- A slice power object satisfies the genuine universal property. -/
def representation :
    ((tensorLeft A).op ⋙ Subobject.presheaf (Over B)).RepresentableBy (obj A) where
  homEquiv := homEquiv A _
  homEquiv_comp := homEquiv_natural A

/-- Every slice of an elementary topos has power objects. -/
@[instance_reducible]
def hasPowerObjects (B : C) : AbstractPower.HasPowerObjects (Over B) where
  powerObject := obj
  representation := representation

end SlicePower
end ToposPort
