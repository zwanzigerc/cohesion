{-# OPTIONS --safe --without-K --cohesion #-}

-- Clients of the crisp truncation eliminator. Claude (Fable), 14 November
-- 2026; fable-impl-22 (HANDOFF-37, item 1; R37-NEXT-IMPLEMENTATION-SLICE-01,
-- section 5).
--
-- Literally --safe: this module and everything it imports. Nothing is
-- postulated; the truncation and the extensionality are parameters. Each
-- section is one of the checks that the handoff asks for.
--   1  the generic theorem at one level, with an ORDINARY ambient
--      proposition and handler
--   2  the legitimate use at a boxed representative, and the boxed cover
--      that follows from it
--   3  the levels zero and one, and a target of the next level through a
--      certificate on the same carrier
-- The refusals are CrispTruncationOrdinaryWitness.agda.fail (an ordinary
-- mere element at the crisp binder) and
-- CrispTruncationOrdinaryStructure.agda.fail (an ordinary structure).
module CrispTruncationExamples where

open import Foundations
open import NativeSharp using (box-crisp-path)
open import SharpPath using (FunExtAt)
open import OrdinaryTruncation
open import CrispTruncation

------------------------------------------------------------------------
-- 1. The proposition, its proof and the handler depend on an ordinary
--    point y in scope. Only A and the mere element are crisp.

module Ambient {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ T : PropTruncation ℓ) where

  open PropTruncation T

  ambient : {@♭ A : Set ℓ} {B : Set ℓ} (P : B → Set ℓ)
          → ((y : B) → IsProp (P y))
          → (y : B) → ((@♭ a : A) → P y) → (@♭ t : ∥ A ∥) → P y
  ambient P P-prop y h t = crisp-trunc-rec fe T (P-prop y) h t

  -- The handler may use its witness where a crisp term is required: here
  -- it is boxed, and the ordinary point y is paired with it.
  with-box : {@♭ A : Set ℓ} {B : Set ℓ} (y : B) → (@♭ t : ∥ A ∥)
           → ∥ ♭ A × B ∥
  with-box y t = crisp-trunc-rec fe T squash (λ a → ∣ box a , y ∣) t

------------------------------------------------------------------------
-- 2. A crisp mere point of a fibre of a crisp map, at a crisp point, gives
--    a mere point of the fibre of flat-map at the boxed point: the
--    representative is boxed, and the path is boxed by box-crisp-path.
--    Then, for a crisp WHOLE cover of the map, every ordinary point of ♭ B
--    merely has a boxed preimage: split the point as a box; at its crisp
--    content the cover is a crisp term. Nothing ordinary is boxed.
--    (SET-ATTACHMENT-AND-BOXED-COVER-01 asks for this at a quotient map;
--    QuotientTruncationExamples has that instance.)

module Boxed {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ T : PropTruncation ℓ) where

  open PropTruncation T

  boxed-representative : {@♭ A B : Set ℓ} (@♭ f : A → B) (@♭ y : B)
                       → (@♭ t : ∥ Fiber f y ∥)
                       → ∥ Fiber (flat-map f) (box y) ∥
  boxed-representative f y t = crisp-trunc-rec fe T squash
    (λ r → ∣ box (fst r) , box-crisp-path (snd r) ∣) t

  boxed-cover : {@♭ A B : Set ℓ} (@♭ f : A → B)
              → (@♭ cover : (y : B) → ∥ Fiber f y ∥)
              → (v : ♭ B) → ∥ Fiber (flat-map f) v ∥
  boxed-cover f cover (box y) = boxed-representative f y (cover y)

------------------------------------------------------------------------
-- 3. Concrete levels.

module LevelZero (@♭ fe : FunExtAt lzero) (@♭ T : PropTruncation lzero)
  where

  open PropTruncation T

  at-zero : {@♭ A : Set} {P : Set} → IsProp P → ((@♭ a : A) → P)
          → (@♭ t : ∥ A ∥) → P
  at-zero = crisp-trunc-rec fe T

module LevelOne (@♭ fe : FunExtAt (lsuc lzero))
  (@♭ T : PropTruncation (lsuc lzero)) where

  open PropTruncation T

  at-one : {@♭ A : Set₁} {P : Set₁} → IsProp P → ((@♭ a : A) → P)
         → (@♭ t : ∥ A ∥) → P
  at-one = crisp-trunc-rec fe T

  -- Into a proposition of level two: the recursor of the same carrier
  -- into that level is an ORDINARY argument. No extensionality at level
  -- two is asked.
  into-two : PropRecInto T (lsuc (lsuc lzero))
           → {@♭ A : Set₁} {P : Set₂} → IsProp P → ((@♭ a : A) → P)
           → (@♭ t : ∥ A ∥) → P
  into-two into = crisp-trunc-rec-into fe T into

  -- The unit law at a crisp point, a path in the proposition.
  at-one-unit : {@♭ A : Set₁} {P : Set₁} (P-prop : IsProp P)
              → (h : (@♭ a : A) → P) (@♭ a : A)
              → at-one P-prop h ∣ a ∣ ≡ h a
  at-one-unit = crisp-trunc-rec-unit fe T
