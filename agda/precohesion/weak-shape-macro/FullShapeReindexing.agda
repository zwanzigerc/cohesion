{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Change of base for full relative shapes: the canonical comparison from
-- the full shape of the reindexed family to the pullback of the given
-- one, with its triangle and its unit law.
-- Claude (Fable), 14 November 2026; fable-impl-23 (HANDOFF-38).
--
-- ShapeReindexing.Comparison for the full interface. The two bases are
-- crisp DISCRETE types; neither is asked to be a set. The pulled total is
-- discrete by DiscretePullback.pullback-discrete, which asks for no
-- sethood; the set-fibre witness of the Shape₀ version has no counterpart
-- because full tests do not ask for one. The given projection and unit
-- are kept: the pulled total is the pullback of the GIVEN carrier.
--
-- Whether the comparison is an equivalence is a hypothesis or a
-- conclusion of theorems elsewhere. Nothing here says that it is.
module FullShapeReindexing where

open import Foundations
open import RelativeSliceShape using (MapOver; over-map; function; triangle)
open import PullbackSetFibers using (transport)
open import DiscretePullback using (Pullback; pullback-discrete)
open import FullRelativeShape

module Comparison
  {@♭ ℓ : Level}
  (@♭ Γ Γ′ : Set ℓ)
  (@♭ Γ-discrete : Discrete Γ)
  (@♭ Γ′-discrete : Discrete Γ′)
  (@♭ A : Γ → Set ℓ)
  (@♭ f : Γ′ → Γ)
  (@♭ shaped : FullShapeOver Γ Γ-discrete A)
  (@♭ reshaped : FullShapeOver Γ′ Γ′-discrete (A ∘ f)) where

  PulledFamily : Γ′ → Set ℓ
  PulledFamily γ′ = FullOutput.family shaped (f γ′)

  PulledTotal : Set ℓ
  PulledTotal = Pullback (FullOutput.projection shaped) f

  pulled-projection : PulledTotal → Γ′
  pulled-projection = fst

  pulled-discrete : Discrete PulledTotal
  pulled-discrete = pullback-discrete
    Γ-discrete Γ′-discrete (FullOutput.total-discrete shaped)
    (FullOutput.projection shaped) f

  -- The given unit, pulled back. Its triangle is refl.
  pulled-unit : MapOver (fst {B = A ∘ f}) pulled-projection
  pulled-unit = over-map
    (λ { (γ′ , a) → γ′ , FullOutput.family-unit shaped (f γ′) a })
    (λ _ → refl)

  -- The canonical comparison, as a whole map over Γ′.
  comparison-over
    : MapOver (FullOutput.projection reshaped) pulled-projection
  comparison-over = FullOutput.factor reshaped PulledTotal pulled-discrete
    pulled-projection pulled-unit

  comparison-total : FullOutput.Total reshaped → PulledTotal
  comparison-total = function comparison-over

  -- Its whole unit law: the function and the triangle.
  comparison-β : FullOutput.pre reshaped PulledTotal pulled-projection
                   comparison-over
               ≡ pulled-unit
  comparison-β = FullOutput.factor-β reshaped PulledTotal pulled-discrete
    pulled-projection pulled-unit

  -- On fibres.
  comparison : (γ′ : Γ′)
             → FullOutput.family reshaped γ′
             → FullOutput.family shaped (f γ′)
  comparison γ′ (z , e) = transport PulledFamily
    (triangle comparison-over z ∙ e) (snd (comparison-total z))

  comparison-on-unit : (γ′ : Γ′) → (a : A (f γ′))
                     → comparison γ′ (FullOutput.family-unit reshaped γ′ a)
                       ≡ FullOutput.family-unit shaped (f γ′) a
  comparison-on-unit γ′ a = ap
    (λ h → transport PulledFamily (triangle h (γ′ , a))
      (snd (function h (γ′ , a))))
    comparison-β

  ComparisonIsEquivalence : Set ℓ
  ComparisonIsEquivalence = (γ′ : Γ′) → IsEquiv (comparison γ′)
