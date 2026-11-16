{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Raised client of ClosedLimitsRaised. Opus, 14 November 2026;
-- opus-closed-limits-01. Nothing is postulated and nothing is declared.
--
-- The plan's case j = i + 1, with the level written i ⊔ lsuc i as the one
-- instantiation writes it: the support P : Set (i ⊔ lsuc i), ORDINARY quotient
-- data, truncation, support and effectivity evidence (only the level i is
-- crisp), and i-small sets X, Y, Z with ordinary maps. The
-- actual i-small pullback is presented through the explicit equivalence
-- with the raised pullback; the raised comparison
--   cP (Pullback f g) → Pullback (cP-map f) (cP-map g)
-- is an equivalence, with its projection and generator laws at
-- AtSupport's unitP and pointP; joint detection holds for i-small maps.
module ClosedLimitsRaisedExamples where

open import Foundations
open import CaptureContext using (Raise; raise)
open import PullbackSetFibers using (Pullback)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import ClosedLimitsRaised using (module AtSupportLimits)

module AtNextLevel {@♭ i : Level} (Q : Quotients (i ⊔ lsuc i))
  (E : Eliminates Q (i ⊔ lsuc i)) (T : PropTruncation (i ⊔ lsuc i))
  (P : Set (i ⊔ lsuc i)) (P-prop : IsProp P) (effective : Effective Q) where

  open AtSupportLimits {i} {lsuc i} Q E T P P-prop effective

  module _ {X Y Z : Set i} (Z-set : IsSet Z) (f : X → Z) (g : Y → Z) where

    open Raised Z-set f g

    -- The explicit presentation of the raised i-small pullback.
    presentation : IsEquiv to
    presentation = to-equiv

    comparison : cP (Pullback f g) → Pullback (cP-map f) (cP-map g)
    comparison = κP

    left-exact : IsEquiv comparison
    left-exact = κP-equiv

    first : (z : cP (Pullback f g))
          → fst (comparison z) ≡ cP-map (λ (d : Pullback f g) → fst d) z
    first = κP-projY

    second : (z : cP (Pullback f g))
           → fst (snd (comparison z)) ≡ cP-map (λ (d : Pullback f g) → fst (snd d)) z
    second = κP-projX

    on-unit : (d : Pullback f g) → comparison (unitP d) ≡ K.inX-point (to (raise d))
    on-unit = κP-unitP

    on-point : (p : P) → comparison (pointP p) ≡ K.inP-point p
    on-point = κP-pointP

  module _ {X Y : Set i} (X-set : IsSet X) (Y-set : IsSet Y) (h : X → Y) where

    open RaisedDetection X-set Y-set h

    -- Ordinary λ-bound open and closed witnesses.
    jointly : (open-equiv : P → IsEquiv h) (closed-equiv : IsEquiv (cP-map h))
            → IsEquiv h
    jointly open-equiv closed-equiv = detectP open-equiv closed-equiv
