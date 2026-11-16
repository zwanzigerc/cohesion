{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The staged route in the Nullstellensatz EXTENSION: the two terminal
-- statements for the whole sources of a diagram, and their transfer to
-- the whole shape data of the direct route. Claude (Fable),
-- 13 November 2026; after fable-impl-14 (HANDOFF-31;
-- DIRECT-CAPTURE-GLOBAL-AXIOM-STAGING-01 section 6). Postulate-free; no
-- reflection; no capture. Nothing of the basic theory imports this module.
--
--   StagedPoints p         the Nullstellensatz statements for the two
--                          closed payloads KX, KY of a product package p
--   LinkPoints fe d p q    whole-pointsX : Nullstellensatz tX
--                          whole-pointsY : Nullstellensatz tY
--                          whole-points  : Nullstellensatz tXY
--
-- The two statements are ORDINARY fields: a proof of one is consumed
-- ordinarily, and nothing ordinary is promoted to crisp data. They are
-- statements about the staged closed payloads (terminal instances, the
-- axiom of the extension); a declaration of one is made by
-- NullstellensatzExtension.declareNullstellensatz in the empty context.
-- The transfers are closed-nullstellensatz and
-- GlobalChoice.transport-nullstellensatz, with the shape data of
-- StagedLink.Link; whole-points is product-nullstellensatz on
-- whole-product.
module StagedPoints where

open import Foundations
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalChoice using (transport-nullstellensatz)
open import NullstellensatzExtension using (module Statement; closed-nullstellensatz)
open import DiagramBundle using (CapturedDiagram)
open import DiagramMetadata
open import StagedLink

data StagedPoints {@♭ ℓ : Level} {@♭ m : DiagramMeta ℓ}
    (@♭ p : StagedProduct m) : Set (lsuc ℓ) where
  staged-points :
    (pointsX : Statement.NAxiom (ProductField.KX p))
    (pointsY : Statement.NAxiom (ProductField.KY p))
    → StagedPoints p

module PointsField {@♭ ℓ : Level} {@♭ m : DiagramMeta ℓ}
  {@♭ p : StagedProduct m} where

  pointsX : StagedPoints p → Statement.NAxiom (ProductField.KX p)
  pointsX (staged-points pointsX _) = pointsX

  pointsY : StagedPoints p → Statement.NAxiom (ProductField.KY p)
  pointsY (staged-points _ pointsY) = pointsY

-- The shape data are named through Link itself, at fe, d and p: a copy of
-- Link opened under the ordinary parameter q would be a function of q and
-- could not be used where crisp shape data are expected.
module LinkPoints
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ d : CapturedDiagram ℓ)
  (@♭ p : StagedProduct (metadata d)) (q : StagedPoints p) where

  whole-pointsX : Nullstellensatz (Link.tX fe d p)
  whole-pointsX = transport-nullstellensatz (Link.sX fe d p) (Link.tX fe d p)
    (closed-nullstellensatz fe (Link.X fe d p) (ProductField.KX p)
      (PointsField.pointsX q))

  whole-pointsY : Nullstellensatz (Link.tY fe d p)
  whole-pointsY = transport-nullstellensatz (Link.sY fe d p) (Link.tY fe d p)
    (closed-nullstellensatz fe (Link.Y fe d p) (ProductField.KY p)
      (PointsField.pointsY q))

  whole-points : Nullstellensatz (Link.tXY fe d p)
  whole-points =
    product-nullstellensatz (Link.tX fe d p) (Link.tY fe d p) (Link.tXY fe d p)
      (Link.whole-product fe d p) whole-pointsX whole-pointsY
