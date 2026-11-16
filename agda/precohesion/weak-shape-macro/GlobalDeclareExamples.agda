{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The basic theory in use: shapes and the closed product axiom.
-- fable-impl-02. No Nullstellensatz is imported here.
module GlobalDeclareExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge; module Existence)
open import GlobalDeclare

-- Closed native types. Their cohesion is left unspecified.
postulate Space₁ Space₂ : Set

s₁ : CapturedShape Space₁
s₁ = shape

s₂ : CapturedShape Space₂
s₂ = shape

s₁₂ : CapturedShape (Space₁ × Space₂)
s₁₂ = shape

K₁ : Closed Space₁
K₁ = C.Output.whole-context s₁

K₂ : Closed Space₂
K₂ = C.Output.whole-context s₂

K₁₂ : Closed (Space₁ × Space₂)
K₁₂ = C.Output.whole-context s₁₂

-- One generated axiom: the canonical comparison of these three payloads is
-- an equivalence.
unquoteDecl product₁₂ = declareProduct product₁₂ K₁ K₂ K₁₂

its-type : ProductStatement.ProductAxiom K₁ K₂ K₁₂
its-type = product₁₂

-- The inverse sends a pair of units to the unit of the pair. No function
-- extensionality: only the existence half of the bridge is involved.
private
  module E₁ = Existence Space₁ K₁
  module E₂ = Existence Space₂ K₂
  module E₁₂ = Existence (Space₁ × Space₂) K₁₂

pair-of-units : (x : Space₁) (y : Space₂)
              → inverse product₁₂ (E₁.η₀ x , E₂.η₀ y) ≡ E₁₂.η₀ (x , y)
pair-of-units x y =
  sym (ap (inverse product₁₂) (ProductStatement.compare₀-η K₁ K₂ K₁₂ x y))
  ∙ retraction product₁₂ (E₁₂.η₀ (x , y))

module WithFunExt (@♭ fe : FunExtAt lzero) where

  d₁ : ShapeData Space₁
  d₁ = closed-bridge fe Space₁ K₁

  d₂ : ShapeData Space₂
  d₂ = closed-bridge fe Space₂ K₂

  d₁₂ : ShapeData (Space₁ × Space₂)
  d₁₂ = closed-bridge fe (Space₁ × Space₂) K₁₂

  preserves₁₂ : PreservesProduct d₁ d₂ d₁₂
  preserves₁₂ = ProductStatement.preserves K₁ K₂ K₁₂ fe product₁₂

  -- Weakening: the closed axiom is used as it stands under a further crisp
  -- context. Nothing is re-declared and nothing new is asserted.
  module UnderContext (@♭ b : Bool) (@♭ A : Set) where
    still : PreservesProduct d₁ d₂ d₁₂
    still = preserves₁₂
