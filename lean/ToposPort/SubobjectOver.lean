/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Subobjects of a slice object and its underlying object -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ToposPort

variable {C : Type u} [Category.{v} C] {B : C}

set_option backward.isDefEq.respectTransparency false

/-- Forget the map to the slice base. -/
def subobjectOverTo (X : Over B) : Subobject X → Subobject X.left :=
  Subobject.lift (fun {A} (f : A ⟶ X) _ => Subobject.mk f.left) (by
    intro A D f g hf hg i h
    exact Subobject.mk_eq_mk_of_comm _ _ ((Over.forget B).mapIso i)
      (congrArg Over.Hom.left h))

@[simp]
lemma subobjectOverTo_mk {X Y : Over B} (f : Y ⟶ X) [Mono f] :
    subobjectOverTo X (Subobject.mk f) = Subobject.mk f.left := rfl

/-- Regard a subobject as an object over the slice base by composition. -/
def subobjectOverFrom (X : Over B) : Subobject X.left → Subobject X :=
  Subobject.lift (fun {A} (f : A ⟶ X.left) _ => Subobject.mk
    (Over.homMk f : Over.mk (f ≫ X.hom) ⟶ X)) (by
      intro A D f g hf hg i h
      apply Subobject.mk_eq_mk_of_comm _ _
        (Over.isoMk i (by
          change i.hom ≫ g ≫ X.hom = f ≫ X.hom
          rw [← Category.assoc, h]))
      exact Over.OverMorphism.ext h)

@[simp]
lemma subobjectOverFrom_mk (X : Over B) {A : C} (f : A ⟶ X.left) [Mono f] :
    subobjectOverFrom X (Subobject.mk f) =
      Subobject.mk (Over.homMk f : Over.mk (f ≫ X.hom) ⟶ X) := rfl

lemma subobjectOverFrom_to (X : Over B) (S : Subobject X) :
    subobjectOverFrom X (subobjectOverTo X S) = S := by
  induction S using Subobject.ind with
  | @h A f hf =>
    simp only [subobjectOverTo_mk, subobjectOverFrom_mk]
    let e : Over.mk (f.left ≫ X.hom) ≅ A := Over.isoMk (Iso.refl A.left) (by simp)
    apply Subobject.mk_eq_mk_of_comm _ _ e
    apply Over.OverMorphism.ext
    simp [e]

lemma subobjectOverTo_from (X : Over B) (S : Subobject X.left) :
    subobjectOverTo X (subobjectOverFrom X S) = S := by
  induction S using Subobject.ind with
  | _ f => simp

/-- Subobjects in `C/B` are precisely subobjects of the underlying object in
`C`, with the same order by inclusion. -/
def subobjectOverEquiv (X : Over B) : Subobject X ≃o Subobject X.left where
  toFun := subobjectOverTo X
  invFun := subobjectOverFrom X
  left_inv := subobjectOverFrom_to X
  right_inv := subobjectOverTo_from X
  map_rel_iff' := by
    intro S T
    change subobjectOverTo X S ≤ subobjectOverTo X T ↔ S ≤ T
    induction S, T using Subobject.ind₂ with
    | _ f g =>
      simp only [subobjectOverTo_mk]
      constructor
      · intro h
        let k := Subobject.ofMkLEMk f.left g.left h
        have hk : k ≫ g.left = f.left := by simp [k]
        apply Subobject.mk_le_mk_of_comm (Over.homMk k (by
          rw [← Over.w g, ← Category.assoc, hk, Over.w f]))
        exact Over.OverMorphism.ext hk
      · intro h
        exact Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk f g h).left
          (congrArg Over.Hom.left (by simp : Subobject.ofMkLEMk f g h ≫ g = f))

@[simp]
lemma subobjectOverEquiv_mk {X Y : Over B} (f : Y ⟶ X) [Mono f] :
    subobjectOverEquiv X (Subobject.mk f) = Subobject.mk f.left := rfl

/-- The equivalence commutes with inverse image. -/
lemma subobjectOverEquiv_pullback [HasPullbacks C] {X Y : Over B} (f : X ⟶ Y) (S : Subobject Y) :
    subobjectOverEquiv X ((Subobject.pullback f).obj S) =
      (Subobject.pullback f.left).obj (subobjectOverEquiv Y S) := by
  induction S using Subobject.ind with
  | _ m =>
    rw [Subobject.pullback_obj_mk (IsPullback.of_hasPullback m f)]
    rw [subobjectOverEquiv_mk, subobjectOverEquiv_mk]
    exact (Subobject.pullback_obj_mk
      ((IsPullback.of_hasPullback m f).map (Over.forget B))).symm

end ToposPort
