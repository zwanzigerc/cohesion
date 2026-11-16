import Mathlib.CategoryTheory.Subterminal
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The closed reflection complementary to a subterminal object

This develops the specific closed reflection needed for the cohesion argument,
rather than porting all of the Lawvere–Tierney sheafification construction from
Bhavik Mehta's Lean 3 `topos` project (`src/sheaf.lean`).

For a subterminal object `P`, a closed object `B` is one for which `P × B → P`
is an isomorphism. Its reflector is `A ⨿_{P × A} P`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ToposPort.ClosedSubtopos

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable (P : C)

/-- Objects of the closed part complementary to `P`. -/
def IsClosed (A : C) : Prop := IsIso (prod.fst : P ⨯ A ⟶ P)

/-- The full category of closed objects. -/
abbrev ClosedObjects := ObjectProperty.FullSubcategory (IsClosed P)

/-- The fully faithful inclusion of the closed part. -/
abbrev inclusion : ClosedObjects P ⥤ C := ObjectProperty.ι _

/-- Over `P`, any two maps into a closed object coincide. -/
theorem closed_hom_ext {A B : C} (hB : IsClosed P B) (p : A ⟶ P)
    (f g : A ⟶ B) : f = g := by
  let : IsIso (prod.fst : P ⨯ B ⟶ P) := hB
  have h : prod.lift p f = prod.lift p g := by
    apply (cancel_mono (prod.fst : P ⨯ B ⟶ P)).1
    simp
  simpa using congrArg (fun k => k ≫ prod.snd) h

/-- The unique map from `P` to a closed object. -/
def point {B : C} (hB : IsClosed P B) : P ⟶ B :=
  letI : IsIso (prod.fst : P ⨯ B ⟶ P) := hB
  inv (prod.fst : P ⨯ B ⟶ P) ≫ prod.snd

variable [HasPushouts C]

/-- The closed reflection, as an object of the ambient category. -/
abbrev object (A : C) := pushout (prod.snd : P ⨯ A ⟶ A) prod.fst

/-- The unit of closed reflection. -/
abbrev unit (A : C) : A ⟶ object P A := pushout.inl _ _

/-- The image of `P` in the closed reflection. -/
abbrev base (A : C) : P ⟶ object P A := pushout.inr _ _

/-- The universal extension of a map into a closed object. -/
def extend {A B : C} (hB : IsClosed P B) (f : A ⟶ B) : object P A ⟶ B :=
  pushout.desc f (point P hB)
    (closed_hom_ext P hB prod.fst _ _)

@[simp, reassoc]
theorem unit_extend {A B : C} (hB : IsClosed P B) (f : A ⟶ B) :
    unit P A ≫ extend P hB f = f := by simp [unit, extend]

theorem extend_unique {A B : C} (hB : IsClosed P B) (f : A ⟶ B)
    (g : object P A ⟶ B) (hg : unit P A ≫ g = f) : g = extend P hB f := by
  apply pushout.hom_ext
  · simpa using hg
  · apply closed_hom_ext P hB (𝟙 P)

/-- Pushout makes the closed-reflection universal property explicit. -/
def homEquiv {A B : C} (hB : IsClosed P B) :
    (object P A ⟶ B) ≃ (A ⟶ B) where
  toFun f := unit P A ≫ f
  invFun f := extend P hB f
  left_inv f := (extend_unique P hB _ f rfl).symm
  right_inv f := unit_extend P hB f

/-- The underlying endofunctor of the closed reflection. -/
def functor : C ⥤ C where
  obj := object P
  map {A B} f := pushout.map _ _ _ _ f (𝟙 P) (prod.map (𝟙 P) f)
    (by simp) (by simp)
  map_id A := by apply pushout.hom_ext <;> simp [pushout.map]
  map_comp f g := by apply pushout.hom_ext <;> simp [pushout.map]

@[simp, reassoc]
theorem unit_map {A B : C} (f : A ⟶ B) :
    unit P A ≫ (functor P).map f = f ≫ unit P B := by
  simp [unit, functor, pushout.map]

@[simp, reassoc]
theorem base_map {A B : C} (f : A ⟶ B) :
    base P A ≫ (functor P).map f = base P B := by
  simp [base, functor, pushout.map]

omit [HasPushouts C] in
/-- Subterminality makes the redundant `P` coordinate invertible. -/
theorem redundant_product_isIso (hP : IsSubterminal P) (A : C) :
    IsIso ((prod.functor.obj P).map (prod.snd : P ⨯ A ⟶ A)) := by
  change IsIso (prod.map (𝟙 P) prod.snd)
  refine ⟨⟨prod.lift prod.fst (𝟙 _), ?_, ?_⟩⟩
  · ext <;> first | exact hP _ _ | simp
  · ext <;> simp

/-- The pushout defining closed reflection is indeed closed.
The sole preservation hypothesis follows from cartesian closure. -/
theorem object_isClosed (hP : IsSubterminal P)
    [PreservesColimitsOfShape WalkingSpan (prod.functor.obj P)] (A : C) :
    IsClosed P (object P A) := by
  let F := prod.functor.obj P
  have := redundant_product_isIso P hP A
  have h := F.map_isPushout (IsPushout.of_hasPushout
    (prod.snd : P ⨯ A ⟶ A) prod.fst)
  have : IsIso (F.map (base P A)) := h.isIso_inr_of_isIso
  have : IsIso (prod.fst : P ⨯ P ⟶ P) := by
    let := hP.isIso_diag
    exact isIso_of_hom_comp_eq_id (diag P) (by simp : diag P ≫ prod.fst = 𝟙 P)
  unfold IsClosed
  exact IsIso.of_isIso_fac_left (f := F.map (base P A))
    (h := (prod.fst : P ⨯ P ⟶ P)) (by simp [F])

/-- Closed objects are precisely fixed objects of the reflector: the easy direction. -/
theorem unit_isIso_of_closed {A : C} (hA : IsClosed P A) : IsIso (unit P A) := by
  let : IsIso (prod.fst : P ⨯ A ⟶ P) := hA
  have h : point P hA ≫ unit P A = base P A := by
    apply (cancel_epi (prod.fst : P ⨯ A ⟶ P)).1
    rw [← Category.assoc]
    rw [closed_hom_ext P hA (prod.fst : P ⨯ A ⟶ P)
      (prod.fst ≫ point P hA) prod.snd]
    exact pushout.condition
  refine ⟨⟨extend P hA (𝟙 A), unit_extend P hA _, ?_⟩⟩
  apply pushout.hom_ext
  · simp [unit, extend]
  · simpa [base, extend] using h

variable [PreservesColimitsOfShape WalkingSpan (prod.functor.obj P)]

/-- The unit is invertible exactly at closed objects. -/
theorem unit_isIso_iff_closed (hP : IsSubterminal P) (A : C) :
    IsIso (unit P A) ↔ IsClosed P A := by
  constructor
  · intro h
    let : IsIso (unit P A) := h
    let : IsIso (prod.fst : P ⨯ object P A ⟶ P) := object_isClosed P hP A
    change IsIso (prod.fst : P ⨯ A ⟶ P)
    have h' : IsIso (prod.map (𝟙 P) (unit P A) ≫ prod.fst) := inferInstance
    simpa using h'
  · exact unit_isIso_of_closed P

/-- The closed reflector, with codomain the full category of closed objects. -/
def reflector (hP : IsSubterminal P) : C ⥤ ClosedObjects P where
  obj A := ⟨object P A, object_isClosed P hP A⟩
  map f := ObjectProperty.homMk ((functor P).map f)
  map_id A := by apply ObjectProperty.hom_ext; exact (functor P).map_id A
  map_comp f g := by apply ObjectProperty.hom_ext; exact (functor P).map_comp f g

/-- The adjunction defining the closed subcategory as a reflection. -/
def adjunction (hP : IsSubterminal P) : reflector P hP ⊣ inclusion P :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B =>
        { toFun := fun f => unit P A ≫ f.hom
          invFun := fun f => ObjectProperty.homMk (extend P B.property f)
          left_inv := fun f => by
            apply ObjectProperty.hom_ext
            exact (extend_unique P B.property _ f.hom rfl).symm
          right_inv := fun f => unit_extend P B.property f }
      homEquiv_naturality_left_symm := by
        intro A A' B f g
        apply ObjectProperty.hom_ext
        apply (homEquiv P B.property).injective
        change unit P A ≫ extend P B.property (f ≫ g) =
          unit P A ≫ (functor P).map f ≫ extend P B.property g
        rw [← Category.assoc, unit_map, Category.assoc, unit_extend, unit_extend]
      homEquiv_naturality_right := by
        intro A B B' f g
        change unit P A ≫ f.hom ≫ g.hom = (unit P A ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }

@[simp]
theorem adjunction_unit (hP : IsSubterminal P) (A : C) :
    (adjunction P hP).unit.app A = unit P A := by
  change unit P A ≫ 𝟙 _ = unit P A
  simp

omit [PreservesColimitsOfShape WalkingSpan (prod.functor.obj P)] in
/-- In a cartesian closed category the requisite pushout preservation is automatic. -/
theorem object_isClosed_of_cartesianClosed [CartesianMonoidalCategory C]
    [MonoidalClosed C] (hP : IsSubterminal P) (A : C) :
    IsClosed P (object P A) := object_isClosed P hP A

end ToposPort.ClosedSubtopos
