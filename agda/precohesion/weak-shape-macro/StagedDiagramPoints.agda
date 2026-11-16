{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The staged route on the dependent Bool/Code diagram, in the
-- Nullstellensatz EXTENSION. Claude (Fable), 13 November 2026; after
-- fable-impl-14 (DIRECT-CAPTURE-GLOBAL-AXIOM-STAGING-01 section 6). This
-- file imports the basic client; the basic client imports nothing of the
-- extension.
--
-- DECLARATIONS OF THIS FILE: two Nullstellensatz statements, in the empty
-- context, one for each of the two staged closed payloads of
-- StagedDiagramClient (terminal instances). No shape is requested here.
module StagedDiagramPoints where

open import Foundations
open import Agda.Builtin.Bool
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import NullstellensatzExtension
open import DependentContextFixtures using (Code)
open import StagedLink
open import StagedPoints
open import StagedDiagramClient

-- USER: the two statements, through the existing entry point.
unquoteDecl pointsX = declareNullstellensatz pointsX KX
unquoteDecl pointsY = declareNullstellensatz pointsY KY

points : StagedPoints package
points = staged-points pointsX pointsY

-- USER: in the context, after function extensionality.
module UsePoints (@♭ b : Bool) (@♭ v : Code b) (@♭ fe : FunExtAt lzero) where

  open Use b v fe using (module L)

  module N = LinkPoints fe (Local.cells b v) package points

  whole-pointsX : Nullstellensatz L.tX
  whole-pointsX = N.whole-pointsX

  whole-pointsY : Nullstellensatz L.tY
  whole-pointsY = N.whole-pointsY

  -- With the product law, for the product as well.
  whole-points : Nullstellensatz L.tXY
  whole-points = N.whole-points
