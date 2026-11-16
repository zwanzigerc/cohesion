{-# OPTIONS --cohesion --without-K --flat-split #-}

-- One closed shape axiom for a total space gives the relative reflection
-- of the family and terminal shape data of every fibre.
-- fable-impl-06; HANDOFF-06 item 6 (converse of R36 in use).
--
-- Family : Bool → Set is a closed family of unspecified closed types
-- (ClosedSliceExamples). The only axiom declared in this file is the one
-- that `shape` declares for the closed total space Σ Bool Family. From
-- it, under function extensionality:
--   total     terminal shape data of Σ Bool Family       (ClosedBridge)
--   relative  the relative reflection of Family over Bool, with the same
--             carrier and unit                           (TotalConverse)
--   fibre b   terminal shape data of Family b at each crisp b, with
--             carrier the fibre of `relative`            (DecidableBase)
-- No product axiom, no Nullstellensatz, no continuity, and no shape axiom
-- for Family true or Family false.
module TotalConverseExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
import RelativeSliceShape as R
open R using (RelativeShapeOver)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge)
open import ClosedSliceExamples using (Family; bool-discrete)
open import DecidableBase
open import OpenContextExamples using (bool-dec)
open import TotalConverse

Total : Set
Total = Σ Bool Family

-- The one axiom: a closed capture of the total space.
captured : CapturedShape Total
captured = shape

K : Closed Total
K = C.Output.whole-context captured

module WithFunExt (@♭ fe : FunExtAt lzero) where

  total : ShapeData Total
  total = closed-bridge fe Total K

  relative : RelativeShapeOver Bool bool-discrete Family
  relative =
    Converse.relative fe {dΓ = bool-discrete} (decidable-set bool-dec) total

  -- Same carrier and unit as the closed shape of the total space.
  same-carrier : R.Output.Total relative ≡ ʃ total
  same-carrier = refl

  same-unit : (a : Total) → R.Output.unit relative a ≡ η total a
  same-unit a = refl

  -- Terminal shape data of each fibre, from that one axiom.
  fibre : (@♭ b : Bool) → ShapeData (Family b)
  fibre b = Fibre.fibre-data fe bool-dec relative b

  -- Its carrier is the fibre of the relative reflection over b.
  fibre-carrier : (@♭ b : Bool) → ʃ (fibre b) ≡ R.Output.family relative b
  fibre-carrier b = refl
