{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Importing client of stage B. Opus, 14 November 2026; opus-closed-limits-01
-- (delta 06). Inhabits Fable's UNCHANGED SetSourceKernelStatements
-- .ClosedComparison.Statement-B at its exact telescope (all data crisp
-- variables), and applies it to crisp decisions to get the comparison on
-- every fibre. Nothing is postulated or declared.
module ClosedComparisonClient where

open import Foundations
open import RelativeSliceShape using (RelativeShapeOver)
open import GlobalPropositions using (FunExt₂)
open import OrdinaryTruncation using (PropTruncation)
open import ClosedReflection using (Closed)
open import SetSourceKernelStatements using (module ClosedComparison)
open import ClosedComparisonProof using (module Proof)

module AtClosedDiagram {@♭ ℓ : Level}
  (@♭ fe : FunExt₂ ℓ ℓ) (@♭ T : PropTruncation ℓ)
  (@♭ P : Set ℓ) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  (@♭ Γ Γ′ : Set ℓ) (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
  (@♭ Γ-set : IsSet Γ) (@♭ Γ′-set : IsSet Γ′)
  (@♭ closed-Γ : Closed P Γ) (@♭ closed-Γ′ : Closed P Γ′)
  (@♭ A : Γ → Set ℓ) (@♭ closed-total : Closed P (Σ Γ A))
  (@♭ g : Γ′ → Γ)
  (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ K′ : RelativeShapeOver Γ′ dΓ′ (A ∘ g)) where

  private
    module S = ClosedComparison fe T P P-prop dP Γ Γ′ dΓ dΓ′ Γ-set Γ′-set
      closed-Γ closed-Γ′ A closed-total g K K′

  statement-B : S.Statement-B
  statement-B = Proof.statement-B fe T P P-prop dP Γ Γ′ dΓ dΓ′ Γ-set Γ′-set
    closed-Γ closed-Γ′ A closed-total g K K′

  module _ (@♭ δ : S.Decision Γ) (@♭ δ′ : S.Decision Γ′) where
    every-fibre : S.C.ComparisonIsEquivalence
    every-fibre = statement-B δ δ′
