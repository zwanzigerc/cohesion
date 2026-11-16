{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The codiscrete power and the comparison of chosen shapes in use.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, the bounded
-- client of section 6, generic part).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters:
--   section 1   crisp F, A : Set ℓ and dF : Discrete F. Nothing else.
--   section 2   in addition crisp fe : FunExt₂ ℓ ℓ
--   section 3   in addition THREE independent crisp shape data
--   section 4   in addition mc : MonoC dF sX sE, an ORDINARY parameter,
--               in a module of its own
module CodiscretePowerExamples where

open import Foundations
open import NativeSharp using (♯; sharp-unit; sharp-extract)
open import GlobalPrecohesion
  using (ShapeData; ʃ; η; κ; MonoC)
open import GlobalPropositions using (FunExt₂)
open import CodiscretePower

------------------------------------------------------------------------
-- 1. The two maps, before any hypothesis.

module Maps {@♭ ℓ : Level} {@♭ F A : Set ℓ} (@♭ dF : Discrete F) where

  open Source {A = A} dF

  forward : ♯ (F → A) → F → ♯ A
  forward = e

  backward : (F → ♯ A) → ♯ (F → A)
  backward = b

  -- On a unit, by computation.
  on-unit : (g : F → A) (x : F) → e (sharp-unit g) x ≡ sharp-unit (g x)
  on-unit g x = refl

  -- At a crisp family and a crisp point, the underlying value of the
  -- backward map is the extracted value: a path, the computation rule of
  -- the induction on F.
  underlying : (@♭ g : F → ♯ A) (@♭ x : F)
             → sharp-extract (b g) x ≡ sharp-extract (g x)
  underlying = b-at

------------------------------------------------------------------------
-- 2. The equivalence.

module Equivalence {@♭ ℓ : Level} {@♭ F A : Set ℓ} (@♭ dF : Discrete F)
  (@♭ fe : FunExt₂ ℓ ℓ) where

  open Inverse {A = A} dF fe

  power : IsEquiv e
  power = e-is-equiv

  -- The inverse of the equivalence is b, by computation.
  inverse-is : (g : F → ♯ A) → inverse e-is-equiv g ≡ b g
  inverse-is g = refl

  -- So a family of units goes back to the unit of the family.
  units-back : (g : F → A) → b (λ x → sharp-unit (g x)) ≡ sharp-unit g
  units-back g = b-e (sharp-unit g)

------------------------------------------------------------------------
-- 3. Three independent shapes, and 4. cancellation.

module Shapes {@♭ ℓ : Level} {@♭ F A : Set ℓ} (@♭ dF : Discrete F)
  (@♭ fe : FunExt₂ ℓ ℓ)
  (@♭ sX : ShapeData (♯ A))
  (@♭ sE : ShapeData (F → ♯ A))
  (@♭ sY : ShapeData (♯ (F → A))) where

  open Transfer {A = A} dF fe sX sE sY

  -- The comparison goes between the ORIGINAL carriers.
  comparison : ʃ sY → ʃ sE
  comparison = alpha

  comparison-is-equiv : IsEquiv alpha
  comparison-is-equiv = alpha-is-equiv

  -- sigma is the existing continuity comparison after it. By computation.
  sigma-is : (s : ʃ sY) → sigma s ≡ κ dF sX sE (alpha s)
  sigma-is s = refl

  -- The unit law, at an ordinary family and an ordinary point.
  on-units : (g : F → A) (x : F)
           → sigma (η sY (sharp-unit g)) x ≡ η sX (sharp-unit (g x))
  on-units = sigma-unit

  module Cancellation (mc : MonoC dF sX sE) where

    cancel : (s t : ʃ sY) → sigma s ≡ sigma t → s ≡ t
    cancel = sigma-injective mc

    -- Two families whose values have the same unit have the same unit.
    same-unit : (g h : F → A)
              → ((x : F) → η sX (sharp-unit (g x)) ≡ η sX (sharp-unit (h x)))
              → η sY (sharp-unit g) ≡ η sY (sharp-unit h)
    same-unit = unit-cong mc
