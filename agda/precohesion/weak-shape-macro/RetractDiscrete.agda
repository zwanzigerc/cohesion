{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A crisp retract of a discrete type is discrete, at INDEPENDENT levels.
-- Claude (Fable), 13 November 2026; after fable-impl-16 (HANDOFF-33 item 1;
-- NEXT-NATIVE-CLASSIFIER-GATE-01 section 1, whose construction this is).
-- Postulate-free; no function extensionality; no sethood; no shape data;
-- no reflection.
--
--   retract-discrete i r h dS : Discrete A
--     for crisp  A : Set a,  S : Set b,  i : A → S,  r : S → A,
--     h : (x : A) → r (i x) ≡ x  and  dS : Discrete S
--
-- The two levels a and b are unrelated.
--
-- Proof. Discrete A says that  counit : ♭ A → A  is an equivalence. Put
--   lift x = flat-map r (inverse dS (i x)) : ♭ A.
-- Then
--   counit (lift x) ≡ r (counit (inverse dS (i x)))   flat-map-counit
--                   ≡ r (i x)                         section of dS, under r
--                   ≡ x                               h
-- so lift is a section of the counit of A, and lift and this law are crisp
-- terms: i, r, h and dS are crisp, and x is a bound ordinary variable.
-- DiscretePullback.counit-section-discrete makes the equivalence from ONE
-- crisp section and its law; the other inverse law and the coherence are
-- its work (the flat modality is idempotent), and nothing of that kind is
-- proved again here.
--
-- Only the retraction law  r ∘ i ≡ id  is asked for, pointwise. Nothing is
-- asked of  i ∘ r, and A is not asked to be a set.
--
-- What it rests on: Foundations (flat-map, flat-map-counit, the definition
-- of Discrete) and DiscretePullback (counit-section-discrete, which matches
-- on a crisp identity and so needs --flat-split). The whole import closure
-- is Foundations, DiscretePullback, FlatContext, PullbackSetFibers and
-- RelativeSliceShape. It is not --safe and does not claim to be.
module RetractDiscrete where

open import Foundations
open import DiscretePullback using (counit-section-discrete)

module Retract
  {@♭ a b : Level} {@♭ A : Set a} {@♭ S : Set b}
  (@♭ i : A → S) (@♭ r : S → A)
  (@♭ h : (x : A) → r (i x) ≡ x)
  (@♭ S-discrete : Discrete S) where

  lift : A → ♭ A
  lift x = flat-map r (inverse S-discrete (i x))

  lift-section : (x : A) → counit (lift x) ≡ x
  lift-section x = flat-map-counit r (inverse S-discrete (i x))
                 ∙ ap r (section S-discrete (i x))
                 ∙ h x

  discrete : Discrete A
  discrete = counit-section-discrete lift lift-section

retract-discrete :
  {@♭ a b : Level} {@♭ A : Set a} {@♭ S : Set b}
  → (@♭ i : A → S) (@♭ r : S → A)
  → (@♭ h : (x : A) → r (i x) ≡ x)
  → (@♭ S-discrete : Discrete S) → Discrete A
retract-discrete = Retract.discrete
