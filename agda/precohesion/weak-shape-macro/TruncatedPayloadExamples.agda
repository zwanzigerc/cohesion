{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Clients of the payload truncation. Claude (Fable), 14 November 2026;
-- fable-impl-22.
--
-- Nothing is postulated and no shape is declared: the payloads, the
-- truncation and the extensionality are crisp parameters.
--   1  The set truncation DERIVED from a supplied quotient structure is
--      accepted by truncate-payload: the call that HANDOFF-37 asks to keep
--      possible.
--   2  For two payloads K and K′ of a reindexing, held as VARIABLES, the
--      canonical comparison of the truncated payloads and that of the
--      original ones have ONE type, by conversion. So the statement
--      "the two comparisons are equal" and the statement of the transfer
--      are well formed. They are only STATED here: their proof is section 4
--      of SHAPE0-TRUNCATE-EXISTING-PAYLOAD-01 and belongs to the proof
--      plan (Opus), not to this increment.
module TruncatedPayloadExamples where

open import Foundations
open import RelativeSliceShape
open import ShapeReindexing using (module Comparison)
open import ShapeChoice using (FunExtAt)
open import OrdinaryTruncation
open import SmallQuotient
open import QuotientTruncations using (module FromQuotients)
open import TruncatedPayload

------------------------------------------------------------------------
-- 1. From a quotient structure.

module FromQuotientStructure {@♭ ℓ : Level} (@♭ Q : Quotients ℓ)
  (@♭ E : Eliminates Q ℓ) (@♭ fe : FunExtAt ℓ)
  {@♭ B : Set ℓ} {@♭ dB : Discrete B} {@♭ A : B → Set ℓ}
  (@♭ K : RelativeShapeOver B dB A) where

  τ : SetTruncation ℓ
  τ = FromQuotients.set-truncation Q E

  open SetTruncation τ
  open Truncate τ fe {B} {dB} {A}

  K₀ : RelativeShapeOver B dB A₀
  K₀ = truncate-payload K

  same-carrier : Output.Total K₀ ≡ Output.Total K
  same-carrier = refl

  unit-law : (b : B) (a : A b)
           → Output.family-unit K₀ b ∣ a ∣₀ ≡ Output.family-unit K b a
  unit-law = unit-β K

------------------------------------------------------------------------
-- 2. One type for the two comparisons.

module SameComparisonType {@♭ ℓ : Level} (@♭ τ : SetTruncation ℓ)
  (@♭ fe : FunExtAt ℓ)
  (@♭ B B′ : Set ℓ) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ A : B → Set ℓ) (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f)) where

  private
    module T = Truncate τ fe {B} {dB} {A}
    module T′ = Truncate τ fe {B′} {dB′} {A ∘ f}

  -- The truncation of the pulled family is the pulled truncation.
  pulled-family : (b′ : B′) → T′.A₀ b′ ≡ T.A₀ (f b′)
  pulled-family b′ = refl

  module C = Comparison B B′ dB dB′ A f K K′
  module C₀ = Comparison B B′ dB dB′ T.A₀ f
    (T.truncate-payload K) (T′.truncate-payload K′)

  same-pulled-total : C₀.PulledTotal ≡ C.PulledTotal
  same-pulled-total = refl

  -- Well formed only because the two types are convertible.
  ComparisonsAgree : Set ℓ
  ComparisonsAgree = C₀.comparison-over ≡ C.comparison-over

  Transfer : Set ℓ
  Transfer = C₀.ComparisonIsEquivalence → C.ComparisonIsEquivalence
