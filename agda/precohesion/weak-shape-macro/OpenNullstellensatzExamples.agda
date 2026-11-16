{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The Nullstellensatz for a fresh capture in an OPEN crisp context, from
-- one CLOSED declared instance. fable-impl-02; FABLE-REVIEW-02.txt, 6.2
-- and 9.2.
--
-- NullstellensatzExamples declares the relative statement once, for the
-- payload of the capture  Whole true . Here b is a crisp variable. The
-- capture  Whole b  has another reflector of the same closed family; the
-- declared statement is moved to it through the shape data of the total
-- (TotalBridge, RelativeNullstellensatz), taken in its fibre form at the
-- current point, and read for the stable shape data of  Family b  itself
-- (DecidableBase). No new axiom is declared in this file.
module OpenNullstellensatzExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
import RelativeSliceShape as R
open import ShapeChoice using (FunExtAt)
open import ClosedSliceExamples using (Family)
open import GlobalPrecohesion
open import GlobalPropositions using (merely-map)
open import DecidableBase
open import TotalBridge
open import NullstellensatzExtension
open import RelativeNullstellensatz
open import NullstellensatzExamples using (Whole; points-family)
open import OpenContextExamples using (bool-dec)

module AtAnyPoint (@♭ fe : FunExtAt lzero) (@♭ b : Bool) where

  private
    s = Whole b
    K = C.Output.whole-context s
    K₀ = C.Output.whole-context (Whole true)
    γ = C.Output.point s
    dec : DecEq (C.Output.context s)
    dec = context-dec bool-dec unit-at-dec

    Γ-set : IsSet (C.Output.context s)
    Γ-set = decidable-set dec

  -- The declared statement, for the reflector used at the current point.
  at-current-reflector : Statement.NAxiom K
  at-current-reflector =
    relative-nullstellensatz fe Γ-set K
      (TotalData.total-data fe Γ-set K₀) points-family

  -- Its fibre form at the current point of the context.
  in-the-fibre : (z : R.Output.family K γ) → Merely (FibrePoint Γ-set K γ z)
  in-the-fibre = fibre-nullstellensatz Γ-set K γ at-current-reflector

  -- Stable shape data of the open type, from the capture alone.
  d : ShapeData (Family b)
  d = CaptureFibre.capture-data fe s dec

  -- Every piece of  Family b  has a crisp point.
  points : Nullstellensatz d
  points z = merely-map convert (in-the-fibre z)
    where
    convert : FibrePoint Γ-set K γ z → Fiber (points-to-pieces d) z
    convert (box v , e) =
      box (C.Output.source-decode s v) ,
      (ap (R.Output.family-unit K γ) (C.Output.source-retraction s v) ∙ e)
