import ToposPort.ClosedSubtopos
import Mathlib.CategoryTheory.Adhesive.Basic

/-!
# The open and closed parts jointly detect isomorphisms

For a subterminal object `P`, product by `P` and the closed reflector
`A ↦ A ⨿_{P × A} P` are jointly conservative in an adhesive category.
This is the categorical open/closed detection principle used in the positive
cohesion proof. The adhesive hypothesis is explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe v u

namespace ToposPort.ClosedSubtopos

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [HasPushouts C]
variable (P : C) (hP : IsSubterminal P)
include hP

omit [HasPushouts C] in
/-- The projection from product with a subterminal is monic. -/
theorem mono_snd (A : C) : Mono (prod.snd : P ⨯ A ⟶ A) where
  right_cancellation f g h := by
    apply prod.hom_ext
    · exact hP _ _
    · exact h

omit hP [HasPushouts C] in
/-- Product projections form a pullback naturality square. -/
theorem product_snd_isPullback {A B : C} (f : A ⟶ B) :
    IsPullback (prod.snd : P ⨯ A ⟶ A) (prod.map (𝟙 P) f) f prod.snd := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro T k l hk hl
    apply prod.hom_ext
    · have hh := congrArg (fun a => a ≫ prod.fst) hl
      simpa using hh
    · exact hk
  · intro T a b h
    refine ⟨prod.lift (b ≫ prod.fst) a, by simp, ?_⟩
    ext
    · simp
    · simpa using h

variable [Adhesive C]

/-- If a map is invertible on the open part, its unit square is a pullback. -/
theorem unit_isPullback {A B : C} (f : A ⟶ B)
    [IsIso ((prod.functor.obj P).map f)] :
    IsPullback (unit P A) f ((functor P).map f) (unit P B) := by
  have := mono_snd P hP B
  have : IsIso (prod.map (𝟙 P) f) :=
    (inferInstance : IsIso ((prod.functor.obj P).map f))
  have hf := product_snd_isPullback P f
  have hg : IsPullback (prod.fst : P ⨯ A ⟶ P)
      (prod.map (𝟙 P) f) (𝟙 P) prod.fst :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have h := Adhesive.van_kampen (IsPushout.of_hasPushout
    (prod.snd : P ⨯ B ⟶ B) prod.fst)
  exact ((h prod.snd prod.fst (unit P A) (base P A)
    (prod.map (𝟙 P) f) f (𝟙 P) ((functor P).map f)
    hf hg ⟨unit_map P f⟩ ⟨by simp⟩
    (IsPushout.of_hasPushout (prod.snd : P ⨯ A ⟶ A) prod.fst).toCommSq).mp
    (IsPushout.of_hasPushout (prod.snd : P ⨯ A ⟶ A) prod.fst)).1

/-- The open and closed restrictions jointly detect isomorphisms. -/
theorem jointly_conservative {A B : C} (f : A ⟶ B)
    [IsIso ((prod.functor.obj P).map f)] [IsIso ((functor P).map f)] :
    IsIso f := (unit_isPullback P hP f).isIso_snd_of_isIso

end ToposPort.ClosedSubtopos
