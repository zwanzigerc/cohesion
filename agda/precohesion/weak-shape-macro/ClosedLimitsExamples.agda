{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Generic ordinary client of ClosedLimits. Opus, 14 November 2026;
-- opus-closed-limits-01. Nothing is postulated and nothing is declared.
--
--   1  At an arbitrary level, with the quotient data, truncation, support
--      and effectivity evidence as ORDINARY variables: the actual comparison
--      κ, its projections (by conversion), its generator laws, IsEquiv κ, the
--      terminal equivalence, joint detection in both forms, and the gap
--      identification of a commutative square.
--   2  The same with the effectivity evidence DERIVED by
--      QuotientEffectivity.OneRow from the next-level elimination, FE and PE
--      (the route a later user may take), and the truncation derived from Q.
module ClosedLimitsExamples where

open import Foundations
open import PullbackSetFibers using (Pullback)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import QuotientTruncations using (One; module FromQuotients)
open import ClosedReflection using (module Reflection)
open import ClosedLimits using (module Limits)

------------------------------------------------------------------------
-- 1. Ordinary variables.

module Generic {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) (P : Set ℓ) (P-prop : IsProp P)
  (effective : Effective Q) where

  open Reflection Q E T P P-prop using (c; c-map; inX; inP)
  open Limits Q E T P P-prop effective

  module _ {X Y Z : Set ℓ} (Z-set : IsSet Z) (f : X → Z) (g : Y → Z) where

    open Comparison Z-set f g

    comparison : c (Pullback f g) → Pullback (c-map f) (c-map g)
    comparison = κ

    first-projection : (z : c (Pullback f g)) → fst (comparison z) ≡ c-map fst z
    first-projection z = refl

    second-projection : (z : c (Pullback f g))
                      → fst (snd (comparison z)) ≡ c-map (λ d → fst (snd d)) z
    second-projection z = refl

    on-inX : (d : Pullback f g) → comparison (inX d) ≡ inX-point d
    on-inX = κ-inX

    on-inP : (p : P) → comparison (inP p) ≡ inP-point p
    on-inP = κ-inP

    left-exact : IsEquiv comparison
    left-exact = κ-equiv

  terminal : IsEquiv (to-one)
  terminal = terminal-equiv

  module _ {X Y : Set ℓ} (X-set : IsSet X) (Y-set : IsSet Y) (h : X → Y) where

    open Detection X-set Y-set h

    -- Both inputs are ordinary λ-bound witnesses.
    jointly : (open-equiv : P → IsEquiv h) (closed-equiv : IsEquiv (c-map h))
            → IsEquiv h
    jointly open-equiv closed-equiv = detect open-equiv closed-equiv

    jointly-product : (e : IsEquiv id×h) (closed-equiv : IsEquiv (c-map h))
                    → IsEquiv h
    jointly-product e closed-equiv = detect-product e closed-equiv

  module _ {W X Y Z : Set ℓ} (Z-set : IsSet Z) (f : X → Z) (g : Y → Z)
    (l : W → X) (r : W → Y) (sq : (w : W) → f (l w) ≡ g (r w)) where

    open Square Z-set f g l r sq

    gap-identified : (z : c W) → Comparison.κ Z-set f g (c-map gap z) ≡ closed-gap z
    gap-identified = closed-gap-identification

------------------------------------------------------------------------
-- 2. Truncation from Q; effectivity a supplied ordinary witness of the
--    type that QuotientEffectivity derives.

module FromQuotient {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (P : Set ℓ) (P-prop : IsProp P) (effective : Effective Q) where

  T : PropTruncation ℓ
  T = FromQuotients.prop-truncation Q E

  open Reflection Q E T P P-prop using (c; c-map)
  open Limits Q E T P P-prop effective

  left-exact : {X Y Z : Set ℓ} (Z-set : IsSet Z) (f : X → Z) (g : Y → Z)
             → IsEquiv (Comparison.κ Z-set f g)
  left-exact Z-set f g = Comparison.κ-equiv Z-set f g

  detect-at : {X Y : Set ℓ} (X-set : IsSet X) (Y-set : IsSet Y) (h : X → Y)
            → (P → IsEquiv h) → IsEquiv (c-map h) → IsEquiv h
  detect-at X-set Y-set h = Detection.detect X-set Y-set h
