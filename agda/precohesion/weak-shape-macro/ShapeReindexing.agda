{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The canonical comparison is derived from the existing whole-slice UP.
-- No further shape axiom, stability axiom, or pullback-closure postulate.
module ShapeReindexing where

open import Foundations
open import RelativeSliceShape
open import PullbackSetFibers using (transport; pullback-set-fibers)
open import DiscretePullback using (Pullback; pullback-discrete)

module Comparison
  {@♭ ℓ : Level}
  (@♭ Γ Γ′ : Set ℓ)
  (@♭ Γ-discrete : Discrete Γ)
  (@♭ Γ′-discrete : Discrete Γ′)
  (@♭ A : Γ → Set ℓ)
  (@♭ f : Γ′ → Γ)
  (@♭ shaped : RelativeShapeOver Γ Γ-discrete A)
  (@♭ reshaped : RelativeShapeOver Γ′ Γ′-discrete (A ∘ f)) where

  PulledFamily : Γ′ → Set ℓ
  PulledFamily γ′ = Output.family shaped (f γ′)

  PulledTotal : Set ℓ
  PulledTotal = Pullback (Output.projection shaped) f

  pulled-projection : PulledTotal → Γ′
  pulled-projection = fst

  pulled-discrete : Discrete PulledTotal
  pulled-discrete = pullback-discrete
    Γ-discrete Γ′-discrete (Output.total-discrete shaped)
    (Output.projection shaped) f

  pulled-set-fibers : SetFibers pulled-projection
  pulled-set-fibers = pullback-set-fibers
    (Output.projection shaped) f (Output.family-set shaped)

  -- Pull the original unit back along f, keeping its triangle over Γ′.
  pulled-unit : MapOver (fst {B = A ∘ f}) pulled-projection
  pulled-unit = over-map
    (λ { (γ′ , a) → γ′ , Output.family-unit shaped (f γ′) a })
    (λ _ → refl)

  comparison-over : MapOver (Output.projection reshaped) pulled-projection
  comparison-over = Output.factor reshaped PulledTotal pulled-discrete
    pulled-projection pulled-set-fibers pulled-unit

  comparison-total : Output.Total reshaped → PulledTotal
  comparison-total = function comparison-over

  -- Fiber form: shape after substitution -> substitution into existing shape.
  comparison : (γ′ : Γ′)
             → Output.family reshaped γ′ → Output.family shaped (f γ′)
  comparison γ′ (z , e) = transport PulledFamily
    (triangle comparison-over z ∙ e) (snd (comparison-total z))

  comparison-on-unit : (γ′ : Γ′) → (a : A (f γ′))
                     → comparison γ′ (Output.family-unit reshaped γ′ a)
                       ≡ Output.family-unit shaped (f γ′) a
  comparison-on-unit γ′ a = ap
    (λ h → transport PulledFamily (triangle h (γ′ , a))
      (snd (function h (γ′ , a))))
    (Output.factor-β reshaped PulledTotal pulled-discrete
      pulled-projection pulled-set-fibers pulled-unit)

  -- The additional conclusion sought in the local-connectedness theorem.
  -- This is a type of evidence, not an assumption or an inhabitant of it.
  ComparisonIsEquivalence : Set ℓ
  ComparisonIsEquivalence = (γ′ : Γ′) → IsEquiv (comparison γ′)

