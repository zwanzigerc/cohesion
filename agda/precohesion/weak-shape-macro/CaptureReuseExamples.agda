{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A named instance seeds the cache; later plain calls reuse its declaration.
-- Every equality below is checked by reduction alone, with no equality axiom.
module CaptureReuseExamples where

open import Foundations
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import CaptureContext using (CrispΣ; CrispUnitAt)

instance
  closed-first : CapturedShape ⊤
  closed-first = shape

closed-second : CapturedShape ⊤
closed-second = shape

closed-same : closed-first ≡ closed-second
closed-same = refl

module Open (@♭ A : Set) where
  instance
    first : CapturedShape A
    first = shape

  -- A mismatch in the registry must not prevent finding an earlier match.
  instance
    other-source : CapturedShape (A → A)
    other-source = shape

  second : CapturedShape A
  second = shape

  same-capture : first ≡ second
  same-capture = refl

  same-whole-context : C.Output.whole-context first ≡ C.Output.whole-context second
  same-whole-context = refl

  same-carrier : C.Output.carrier first ≡ C.Output.carrier second
  same-carrier = refl

  same-unit : C.Output.unit first ≡ C.Output.unit second
  same-unit = refl

  use-directly : C.Output.carrier first → C.Output.carrier second
  use-directly x = x

-- Function-local crisp variables are captured, just like module parameters.
instance
  local-first : {@♭ A : Set} → CapturedShape {ℓ = lsuc lzero} A
  local-first {A} = shape

local-second : (@♭ A : Set) → CapturedShape {ℓ = lsuc lzero} A
local-second B = shape

local-same : (@♭ A : Set) → local-first {A} ≡ local-second A
local-same A = refl

module Dependent
  (@♭ A : Set) (@♭ B : A → Set) (@♭ x : A) (@♭ y : B x) where
  instance
    first : CapturedShape (B x)
    first = shape

  second : CapturedShape (B x)
  second = shape

  same : first ≡ second
  same = refl

  -- The unused final variable remains in the key.
  entire-context : C.Output.context first ≡
    CrispΣ Set (λ A →
    CrispΣ (A → Set) (λ B →
    CrispΣ A (λ x →
    CrispΣ (B x) (λ y → CrispUnitAt (lsuc lzero)))))
  entire-context = refl

module Hidden {@♭ A : Set} {@♭ B : A → Set} {@♭ x : A} where
  instance
    first : CapturedShape (B x)
    first = shape

  second : CapturedShape (B x)
  second = shape

  same : first ≡ second
  same = refl

module Higher (@♭ A : Set₁) where
  instance
    first : CapturedShape A
    first = shape

  second : CapturedShape A
  second = shape

  same : first ≡ second
  same = refl
