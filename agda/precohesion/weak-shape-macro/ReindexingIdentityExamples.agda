{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The identity laws of the canonical comparisons in use. Claude (Fable),
-- 13 November 2026; after fable-impl-17 (HANDOFF-34 item 1, the one
-- bounded client).
--
-- The two reflections are the whole-context payloads of the two
-- INDEPENDENT captures of ShapeChoiceExamples.Calls: one source A, one
-- crisp context (@♭ A : Set), two requests, two generated axioms. Their
-- base is the packed context of a crisp type variable, at level 1. It is
-- discrete and is NOT assumed to be a set: nothing below asks that.
--
-- SUPPLIED DATA. Declared in this file: nothing. Imported with its own
-- declarations: ShapeChoiceExamples, two captures in the context
-- (@♭ A : Set). Hypothesis: function extensionality at level 1, crisp, a
-- module parameter, as in ShapeChoiceExamples.Agreement. The first section
-- takes no extensionality.
module ReindexingIdentityExamples where

open import Foundations
import CapturedShape as C
import RelativeSliceShape as R
open import ShapeChoice using (FunExtAt; id-over; module FiberChoice)
open import ShapeReindexing using (module Comparison)
open import ReindexingIdentity
open import ShapeChoiceExamples using (module Calls)

------------------------------------------------------------------------
-- 1. Without extensionality: the unit of a capture factors through itself
--    by the identity.

module NoExtensionality (@♭ A : Set) where

  private
    K = C.Output.whole-context (Calls.first A)

  self-factor :
    R.Output.factor K (R.Output.Total K) (R.Output.total-discrete K)
      (R.Output.projection K) (R.Output.family-set K)
      (R.over-map (R.Output.unit K) (R.Output.unit-over K))
    ≡ id-over (R.Output.projection K)
  self-factor = SelfChoice.factor-unit K

------------------------------------------------------------------------
-- 2. With extensionality at the level of the data.

module Client (@♭ fe : FunExtAt (lsuc lzero)) (@♭ A : Set) where

  Γ : Set₁
  Γ = C.Output.context (Calls.first A)

  dΓ : Discrete Γ
  dΓ = C.Output.context-discrete (Calls.first A)

  Â : Γ → Set₁
  Â = C.Output.family (Calls.first A)

  -- Two choices of the reflection of Â over Γ.
  K L : R.RelativeShapeOver Γ dΓ Â
  K = C.Output.whole-context (Calls.first A)
  L = C.Output.whole-context (Calls.second A)

  -- The canonical comparison along the identity of Γ, from L to K, and
  -- the canonical comparison of the two choices.
  module I = Comparison Γ Γ dΓ dΓ Â id K L
  module F = FiberChoice fe L K

  -- THE IDENTITY LAW for two choices, at every point of every fibre.
  agrees : (γ : Γ) (w : R.Output.family L γ)
         → I.comparison γ w ≡ F.forward γ w
  agrees = IdentityComparison.identity-choice fe Γ dΓ Â K L

  invertible : (γ : Γ) → IsEquiv (I.comparison γ)
  invertible =
    IdentityComparison.identity-comparison-is-equivalence fe Γ dΓ Â K L

  -- At the captured point it is a map between the two carriers, and it
  -- preserves the units (the unit law that ShapeReindexing already has).
  at-point : C.Output.carrier (Calls.second A) → C.Output.carrier (Calls.first A)
  at-point = I.comparison (C.Output.point (Calls.first A))

  at-point-on-unit : (a : A)
    → at-point (C.Output.unit (Calls.second A) a)
      ≡ C.Output.unit (Calls.first A) a
  at-point-on-unit a = I.comparison-on-unit (C.Output.point (Calls.first A))
    (C.Output.source-embed (Calls.first A) a)

  -- THE IDENTITY LAW for one choice: fibre form and total form.
  module J = Comparison Γ Γ dΓ dΓ Â id K K

  same : (γ : Γ) (w : R.Output.family K γ) → J.comparison γ w ≡ w
  same = IdentityLaw.identity-fibre fe Γ dΓ Â K

  same-total : (z : R.Output.Total K)
             → J.comparison-total z ≡ (R.Output.projection K z , (z , refl))
  same-total = IdentityLaw.identity-total fe Γ dΓ Â K

  -- The comparison of a choice with itself, and of K with K through L.
  self : (γ : Γ) (w : R.Output.family K γ)
       → FiberChoice.forward fe K K γ w ≡ w
  self = ChoiceIdentity.fibre-choice-id fe K

  through : (γ : Γ) (w : R.Output.family K γ)
          → FiberChoice.forward fe L K γ (FiberChoice.forward fe K L γ w) ≡ w
  through γ w = sym (ChoiceComposition.fibre-choice-compose fe K L K γ w)
              ∙ self γ w
