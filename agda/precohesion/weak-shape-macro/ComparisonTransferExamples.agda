{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Clients of the comparison transfer. Opus, 14 November 2026;
-- opus-shape0-main-01. Nothing is postulated and nothing is declared.
--
--   1  At M22's telescope TruncatedPayloadExamples.SameComparisonType,
--      with the payloads, τ and fe as crisp VARIABLES: the actual exports
--      inhabit M22's own statement types ComparisonsAgree and Transfer
--      (written through SameComparisonType, not through ComparisonTransfer),
--      and the transfer is applied to an ORDINARY λ-bound input witness.
--   2  The same with the set truncation DERIVED from a supplied quotient
--      structure (QuotientTruncations.FromQuotients.set-truncation), the
--      route that HANDOFF-37 keeps open.
module ComparisonTransferExamples where

open import Foundations
open import RelativeSliceShape
open import ShapeChoice using (FunExtAt)
open import OrdinaryTruncation using (SetTruncation)
open import SmallQuotient using (Quotients; Eliminates)
open import QuotientTruncations using (module FromQuotients)
import TruncatedPayloadExamples as M22
open import ComparisonTransfer using (module Proof)

------------------------------------------------------------------------
-- 1. Variable payloads at the stated telescope.

module AtStatedTelescope {@♭ ℓ : Level} (@♭ τ : SetTruncation ℓ)
  (@♭ fe : FunExtAt ℓ)
  (@♭ B B′ : Set ℓ) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ A : B → Set ℓ) (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f)) where

  private
    module S = M22.SameComparisonType τ fe B B′ dB dB′ A f K K′
    module P = Proof τ fe B B′ dB dB′ A f K K′

  agree : S.ComparisonsAgree
  agree = P.comparisons-agree

  agree-on-records : S.C₀.comparison-over ≡ S.C.comparison-over
  agree-on-records = P.comparisons-agree

  transfer : S.Transfer
  transfer = P.transfer

  -- The input equivalence is an ordinary argument.
  transfer-ordinary : (w : S.C₀.ComparisonIsEquivalence)
                    → S.C.ComparisonIsEquivalence
  transfer-ordinary w = P.transfer w

  fibres : (γ′ : B′) → S.C₀.comparison γ′ ≡ S.C.comparison γ′
  fibres = P.comparison-fibres-agree

------------------------------------------------------------------------
-- 2. With the set truncation derived from a quotient structure.

module FromQuotientStructure {@♭ ℓ : Level} (@♭ Q : Quotients ℓ)
  (@♭ E : Eliminates Q ℓ) (@♭ fe : FunExtAt ℓ)
  (@♭ B B′ : Set ℓ) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ A : B → Set ℓ) (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f)) where

  τ : SetTruncation ℓ
  τ = FromQuotients.set-truncation Q E

  private
    module S = M22.SameComparisonType τ fe B B′ dB dB′ A f K K′
    module P = Proof τ fe B B′ dB dB′ A f K K′

  agree : S.ComparisonsAgree
  agree = P.comparisons-agree

  transfer : S.Transfer
  transfer = P.transfer
