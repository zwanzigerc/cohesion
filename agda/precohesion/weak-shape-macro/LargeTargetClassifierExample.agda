{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The actual mixed-level classifier map on closed generated shapes, at
-- i = 0. fable-impl-03; HANDOFF-06 item 5 ("actual mixed classifier
-- naturality T(forall_i), not only the Raise example"); acceptance probe 6
-- of CLASSIFIER-LARGE-UP-SCHEMA-01.txt.
--
--   Ω₀ = Ω 0 : Set₁        A₀ = F → Ω₀ : Set₁        B₀ = Ω 1 : Set₂
--   T A₀ = carrier of the shape of ♯ A₀ : Set₁   (small)
--   T B₀ = carrier of the shape of ♯ B₀ : Set₂
--   T∀ : T A₀ → T B₀ ,   T∀ (unit φ) ≡ unit (∀F φ)
--
-- Axioms declared in this file: three closed shapes (of ♯ Ω₀, ♯ A₀, ♯ B₀)
-- and ONE large-target certificate, for the shape of ♯ A₀ at ceiling 2.
-- Everything up to and including the certificate is declared before any
-- extensionality is in scope: the top class F is a closed type built from
-- ClosedBridge.Existence of the shape of ♯ Ω₀. The map ∀F needs
-- FunExt₂ 1 0 (a product of propositions is a proposition); it is a MAP
-- that the certificate consumes, not a source that is reflected.
module LargeTargetClassifierExample where

open import Foundations
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion using (Closed)
open import GlobalPropositions using (FunExt₂)
open import ClosedBridge using (module Existence)
import RelativeSliceShape as R
open import LargeTargetDeclare
open import LargeTargetClassifier

private
  ℓ₁ ℓ₂ : Level
  ℓ₁ = lsuc lzero
  ℓ₂ = lsuc ℓ₁

Ω₀ : Set₁
Ω₀ = Ω lzero

sΩ : CapturedShape (♯ Ω₀)
sΩ = shape

KΩ : Closed (♯ Ω₀)
KΩ = C.Output.whole-context sΩ

private
  module EΩ = Existence (♯ Ω₀) KΩ

-- The top class of the selected shape of ♯ Ω₀: a closed type.
module Top = TopClass {i = lzero} EΩ.T EΩ.η₀
open Top using (F; ∀F)

A₀ : Set₁
A₀ = F → Ω₀

B₀ : Set₂
B₀ = Ω ℓ₁

sA : CapturedShape (♯ A₀)
sA = shape

KA : Closed (♯ A₀)
KA = C.Output.whole-context sA

sB : CapturedShape (♯ B₀)
sB = shape

KB : Closed (♯ B₀)
KB = C.Output.whole-context sB

-- ONE certificate: the small carrier of the shape of ♯ A₀, at ceiling 2.
unquoteDecl upA = declareLargeUP upA ℓ₂ (♯ A₀) KA

private
  module EA = Existence (♯ A₀) KA
  module EB = Existence (♯ B₀) KB

-- The carrier of the domain stays in Set₁, the codomain is in Set₂.
T-A₀ : Set₁
T-A₀ = EA.T

T-B₀ : Set₂
T-B₀ = EB.T

module WithFunExt (@♭ fe : FunExt₂ ℓ₁ lzero) where

  private
    module N = Top.Natural EA.T EA.η₀ upA
                 EB.T EB.T-set (R.Output.total-discrete KB) EB.η₀ fe

  T∀ : T-A₀ → T-B₀
  T∀ = N.T∀

  T∀-natural : (φ : A₀)
             → T∀ (EA.η₀ (sharp-unit φ)) ≡ EB.η₀ (sharp-unit (∀F fe φ))
  T∀-natural = N.T∀-natural

-- The same statement under a second, independent extensionality input: the
-- carriers, the units and the certificate are the same terms.
module TwoInputs (@♭ fe fe′ : FunExt₂ ℓ₁ lzero) where

  private
    module One = WithFunExt fe
    module Other = WithFunExt fe′

  same-domain : T-A₀ ≡ T-A₀
  same-domain = refl

  both : (φ : A₀)
       → (One.T∀ (EA.η₀ (sharp-unit φ)) ≡ EB.η₀ (sharp-unit (∀F fe φ)))
       × (Other.T∀ (EA.η₀ (sharp-unit φ)) ≡ EB.η₀ (sharp-unit (∀F fe′ φ)))
  both φ = One.T∀-natural φ , Other.T∀-natural φ
