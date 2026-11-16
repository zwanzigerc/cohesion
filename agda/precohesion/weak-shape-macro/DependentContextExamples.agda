{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A fresh capture in a DEPENDENT crisp context, turned into terminal
-- shape data at the current point. fable-impl-06; HANDOFF-06 item 6.
--
-- The context is (@♭ b : Bool) (@♭ v : Code b): the type of the second
-- variable depends on the first. Its packed context
--   CrispΣ Bool (λ b → CrispΣ (Code b) (λ _ → CrispUnitAt lzero))
-- has decidable equality by DecidableTelescope.dependent-context-dec, and
-- DecidableBase.CaptureFibre then gives shape data of the source type
-- with the carrier of the capture. No new axiom is declared here beyond
-- the one that `shape` declares; no product axiom, no Nullstellensatz, no
-- continuity. Companion of OpenContextExamples, which has the
-- non-dependent case.
module DependentContextExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import DecidableBase
open import DecidableTelescope
open import OpenContextExamples using (bool-dec)
open import DependentContextFixtures

-- The capture is made in the context of the two term variables alone
-- (OpenContextExamples explains why the extensionality hypothesis must
-- stay out of it).
module Shapes (@♭ b : Bool) (@♭ v : Code b) where

  s : CapturedShape (Source b v)
  s = shape

module Open (@♭ fe : FunExtAt lzero) (@♭ b : Bool) (@♭ v : Code b) where

  open Shapes b v

  d : ShapeData (Source b v)
  d = CaptureFibre.capture-data fe s
        (dependent-context-dec bool-dec
          (λ b′ → context-dec (code-dec b′) unit-at-dec))

  -- The carrier of the data is the carrier of the capture, on the nose.
  same-carrier : ʃ d ≡ C.Output.carrier s
  same-carrier = refl

-- The same at two different points of the context: the data are those of
-- the respective fibres.
at-true-false : (@♭ fe : FunExtAt lzero) → ShapeData ⊤
at-true-false fe = Open.d fe true false

at-false : (@♭ fe : FunExtAt lzero) → ShapeData (Bool × Bool)
at-false fe = Open.d fe false tt
