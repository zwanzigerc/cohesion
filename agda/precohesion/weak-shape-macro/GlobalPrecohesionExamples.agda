{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The whole path from the macro to a consumer of the global axioms.
-- Claude (Fable), 12 November 2026; fable-impl-01.
--
--   shape (empty context)  →  Closed X  →  ShapeData X  →  theorem
--
-- The only axioms in this file are the four constants that `shape`
-- declares. Product preservation and the Nullstellensatz are HYPOTHESES of
-- the consumer module; no instance of them is declared.
module GlobalPrecohesionExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import ClosedSliceExamples using (bool-set; bool-discrete)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge)

-- Closed native types. Their cohesion is left unspecified.
postulate Space₁ Space₂ : Set

s₁ : CapturedShape Space₁
s₁ = shape

s₂ : CapturedShape Space₂
s₂ = shape

s₁₂ : CapturedShape (Space₁ × Space₂)
s₁₂ = shape

s⊤ : CapturedShape ⊤
s⊤ = shape

sBool : CapturedShape Bool
sBool = shape

-- In the empty context the declared payload is the closed one, by
-- computation: these definitions are checked by unfolding only.
K₁ : Closed Space₁
K₁ = C.Output.whole-context s₁

K₂ : Closed Space₂
K₂ = C.Output.whole-context s₂

K₁₂ : Closed (Space₁ × Space₂)
K₁₂ = C.Output.whole-context s₁₂

module WithFunExt (@♭ fe : FunExtAt lzero) where

  d₁ : ShapeData Space₁
  d₁ = closed-bridge fe Space₁ K₁

  d₂ : ShapeData Space₂
  d₂ = closed-bridge fe Space₂ K₂

  d₁₂ : ShapeData (Space₁ × Space₂)
  d₁₂ = closed-bridge fe (Space₁ × Space₂) K₁₂

  d⊤ : ShapeData ⊤
  d⊤ = closed-bridge fe ⊤ (C.Output.whole-context s⊤)

  dBool : ShapeData Bool
  dBool = closed-bridge fe Bool (C.Output.whole-context sBool)

  -- Theorems of the shape data alone.
  pieces-of-point : IsContr (ʃ d⊤)
  pieces-of-point = shape-of-unit d⊤

  pieces-of-Bool : (z : ʃ dBool)
                 → η dBool (back bool-set bool-discrete dBool z) ≡ z
  pieces-of-Bool = η-back bool-set bool-discrete dBool

  -- The comparison maps exist without any further axiom.
  product-comparison : ʃ d₁₂ → ʃ d₁ × ʃ d₂
  product-comparison = compare d₁ d₂ d₁₂

  -- A consumer: the global axioms enter as hypotheses about these objects.
  module Consumer
    (preserves : PreservesProduct d₁ d₂ d₁₂)
    (points₁ : Nullstellensatz d₁) (points₂ : Nullstellensatz d₂) where

    points₁₂ : Nullstellensatz d₁₂
    points₁₂ = product-nullstellensatz d₁ d₂ d₁₂ preserves points₁ points₂
