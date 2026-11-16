{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The Nullstellensatz extension in use. fable-impl-02.
-- This file imports the basic example; the basic example imports nothing
-- from the extension.
module NullstellensatzExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge)
open import GlobalDeclare
open import NullstellensatzExtension
open import GlobalDeclareExamples

-- Terminal instances: one proposition per closed payload.
unquoteDecl points₁ = declareNullstellensatz points₁ K₁
unquoteDecl points₂ = declareNullstellensatz points₂ K₂

-- A relative instance. The reflection is over the packed context of the
-- crisp variable b; the declared statement is about its whole total space.
-- (The family is imported: a postulate of this file could not be captured
-- under a crisp variable.)
open import ClosedSliceExamples using (Family)

Whole : (@♭ b : Bool) → CapturedShape (Family b)
Whole b = shape

unquoteDecl points-family =
  declareNullstellensatz points-family (C.Output.whole-context (Whole true))

type-of-points-family : Statement.NAxiom (C.Output.whole-context (Whole true))
type-of-points-family = points-family

module WithPoints (@♭ fe : FunExtAt lzero) where
  open GlobalDeclareExamples.WithFunExt fe

  -- The consumer of M1, now fed by declared instances: with product
  -- preservation the Nullstellensatz passes to the product.
  points₁₂ : Nullstellensatz d₁₂
  points₁₂ = product-nullstellensatz d₁ d₂ d₁₂ preserves₁₂
    (closed-nullstellensatz fe Space₁ K₁ points₁)
    (closed-nullstellensatz fe Space₂ K₂ points₂)
