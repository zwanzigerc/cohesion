{-# OPTIONS --cohesion --without-K --flat-split #-}

module DeclareCapturedExamples where

open import Foundations
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import DeclareCapturedShape using (declareShape)
open import CaptureContext using (CrispΣ; CrispUnitAt)
open import CaptureFixtures using (CrispArrow)

unquoteDecl closed = declareShape closed ⊤

closed-again : CapturedShape ⊤
closed-again = shape

closed-same : closed ≡ closed-again
closed-same = refl

module Open (@♭ A : Set) where
  unquoteDecl first = declareShape first A

  second : CapturedShape A
  second = shape

  unquoteDecl third = declareShape third A

  same : first ≡ second
  same = refl

  declared-same : first ≡ third
  declared-same = refl

  use-directly : C.Output.carrier first → C.Output.carrier second
  use-directly x = x

module Dependent
  (@♭ A : Set) (@♭ B : A → Set) (@♭ x : A) (@♭ y : B x) where
  unquoteDecl first = declareShape first (B x)

  second : CapturedShape (B x)
  second = shape

  same : first ≡ second
  same = refl

  entire-context : C.Output.context first ≡
    CrispΣ Set (λ A →
    CrispΣ (A → Set) (λ B →
    CrispΣ A (λ x →
    CrispΣ (B x) (λ y → CrispUnitAt (lsuc lzero)))))
  entire-context = refl

module NamedCrispFunction (@♭ A : Set) where
  unquoteDecl first = declareShape first (CrispArrow A A)

  second : CapturedShape (CrispArrow A A)
  second = shape

  same : first ≡ second
  same = refl

local-agreement : (@♭ A : Set) →
  Σ (CapturedShape {ℓ = lsuc lzero} A) (λ first →
  Σ (CapturedShape {ℓ = lsuc lzero} A) (λ second → first ≡ second))
local-agreement A = first , second , refl
  where
  unquoteDecl first = declareShape first A
  second : CapturedShape A
  second = shape

module Higher (@♭ A : Set₁) where
  unquoteDecl first = declareShape first A

  second : CapturedShape A
  second = shape

  same : first ≡ second
  same = refl
