{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Fresh captures in an OPEN crisp context, used directly.
-- Claude (Fable), 13 November 2026; fable-impl-02.
-- GENERIC-THEOREM-ROADMAP-AUDIT-01, gate G4 for decidable set contexts.
--
-- The module Open has a crisp TERM parameter b : Bool and captures shapes
-- of types that depend on b. From each capture, and nothing else, it obtains
-- terminal-style shape data of the source type at the current point b
-- (DecidableBase.CaptureFibre). Those data are what the hypothesis-
-- parameterised theorems of GlobalPrecohesion take. So those theorems are
-- used here on fresh contextual shapes, with no closed re-declaration and no
-- manual diagram parameters.
--
-- No product, Nullstellensatz or continuity axiom is used to get the data.
-- Where a theorem needs product preservation or the Nullstellensatz, they
-- remain hypotheses about the data at hand (module Consumer).
module OpenContextExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import ClosedSliceExamples using (Family; ReindexedFamily)
open import GlobalPrecohesion
open import DecidableBase

-- fable-impl-10: the definition is in BoolDecidable (a module without
-- declarations) and is re-exported here under its old name.
open import BoolDecidable public using (bool-dec)

-- Fresh captures in the context of the TERM parameter alone. Their payloads
-- are reflections over the packed context of b, not closed payloads.
--
-- The captures are made here and not inside `Open` below for a reason: a
-- capture packs EVERY crisp variable in scope. Inside `Open` that would
-- include the extensionality hypothesis fe, whose type lives one universe
-- up and has no decidable equality. Proof-like hypotheses must stay out of
-- the context in which a shape is formed.
module Shapes (@♭ b : Bool) where

  s₁ : CapturedShape (Family b)
  s₁ = shape

  s₂ : CapturedShape (ReindexedFamily b)
  s₂ = shape

  s₁₂ : CapturedShape (Family b × ReindexedFamily b)
  s₁₂ = shape

module Open (@♭ fe : FunExtAt lzero) (@♭ b : Bool) where

  open Shapes b

  -- Shape data of the source types at the current point, from the captures.
  d₁ : ShapeData (Family b)
  d₁ = CaptureFibre.capture-data fe s₁ (context-dec bool-dec unit-at-dec)

  d₂ : ShapeData (ReindexedFamily b)
  d₂ = CaptureFibre.capture-data fe s₂ (context-dec bool-dec unit-at-dec)

  d₁₂ : ShapeData (Family b × ReindexedFamily b)
  d₁₂ = CaptureFibre.capture-data fe s₁₂ (context-dec bool-dec unit-at-dec)

  -- The carrier of the data is the carrier of the capture, on the nose.
  same-carrier : ʃ d₁ ≡ C.Output.carrier s₁
  same-carrier = refl

  -- The canonical comparison of the three contextual shapes exists.
  comparison : ʃ d₁₂ → ʃ d₁ × ʃ d₂
  comparison = compare d₁ d₂ d₁₂

  comparison-on-units : (x : Family b) (y : ReindexedFamily b)
                      → comparison (η d₁₂ (x , y)) ≡ (η d₁ x , η d₂ y)
  comparison-on-units = compare-η d₁ d₂ d₁₂

  -- A theorem of GlobalPrecohesion applied to the contextual shapes. Its
  -- inputs are hypotheses here: whether the comparison of THESE same-context
  -- shapes is invertible is not asserted by any schema.
  module Consumer
    (preserves : PreservesProduct d₁ d₂ d₁₂)
    (points₁ : Nullstellensatz d₁) (points₂ : Nullstellensatz d₂) where

    points₁₂ : Nullstellensatz d₁₂
    points₁₂ = product-nullstellensatz d₁ d₂ d₁₂ preserves points₁ points₂
