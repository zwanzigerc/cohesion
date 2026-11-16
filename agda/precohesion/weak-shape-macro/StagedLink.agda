{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The staged route, LINK: a package of closed declarations for the two
-- whole sources of a diagram, and its use inside the context of the
-- diagram. Claude (Fable), 13 November 2026; after fable-impl-14
-- (HANDOFF-31; DIRECT-CAPTURE-GLOBAL-AXIOM-STAGING-01 sections 5 and 6;
-- FABLE-REVIEW-06-ADDENDUM-01 section 3.3). Postulate-free; no reflection;
-- no capture. BASIC theory: the Nullstellensatz is not imported here
-- (StagedPoints).
--
--   StagedProduct m        closed payloads of  X = WholeB m,  Y = WholeC m
--                          and  X × Y,  and the product statement about
--                          those three payloads
--   ProductField           its accessors
--   Link fe d p            for a bundle d and a package p for the metadata
--                          of d: the three whole shape data and the
--                          product law for them
--
-- A PACKAGE IS VALID FOR ITS CANDIDATE, AND THAT IS ALL IT SAYS. In the
-- staged route its index m is a candidate that the reader admitted, a
-- closed metadata term, and its fields are declarations about the closed
-- types WholeB m and WholeC m, each admissible on its own through the
-- existing entry points (a capture in the empty context;
-- GlobalDeclare.declareProduct). That m is closed is a property of that
-- route and of the guards of those entry points. The type StagedProduct m
-- does NOT encode it: the type is formed at any crisp metadata term.
-- Nor does a value of StagedProduct m say that any descriptor has the
-- index m. The package type has the whole metadata as parameter, the map
-- included, so packages at two metadata terms are different types
-- whenever the two terms are NOT CONVERTIBLE: for instance when their
-- maps are not, under a constant family (StagedDiagramMaps).
-- (fable-impl-16: "not convertible" replaces "differ", and the sentence
-- on closure is new; M15-SOURCE-REVIEW-01.)
--
-- THE LINK. Link takes the bundle and a package for  metadata d . Its
-- application in the context of the diagram is checked by Agda there:
-- the type of the supplied package must convert to
-- StagedProduct (metadata d). A package for another candidate is refused
-- at that point; nothing staged earlier is changed, repaired or retracted
-- by that, and an axiom that was declared for a candidate remains an
-- axiom about that candidate's closed sources.
--
-- WHAT THE LINK GIVES, with fe crisp:
--   sX sY sXY    the staged closed choices, bridged (ClosedBridge)
--   tX tY        the whole shape data DERIVED from the two contextual
--                captures of the bundle (AssembleCaptured.derivedB,
--                derivedC): the direct route's own choices
--   tXY          the staged choice for the product; there is no
--                contextual capture of X × Y
--   whole-product : PreservesProduct tX tY tXY
-- by ProductStatement.preserves and GlobalChoice.ProductChoice. The
-- transfer uses the universal properties of all the supplied shape data
-- and identifies no two choices: the contextual payloads are not made
-- closed, no capture of a fibre is promoted, and nothing is assumed about
-- products over a shared context. whole-product is the canonical
-- comparison of tX, tY, tXY being an equivalence; with crisp inputs it is
-- usable crisply.
module StagedLink where

open import Foundations
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge)
open import GlobalDeclare using (module ProductStatement)
open import GlobalChoice using (module ProductChoice)
open import DiagramBundle using (CapturedDiagram; module AssembleCaptured)
open import DiagramMetadata

data StagedProduct {@♭ ℓ : Level} (@♭ m : DiagramMeta ℓ) : Set (lsuc ℓ) where
  staged-product :
    (@♭ KX : Closed (WholeB m)) (@♭ KY : Closed (WholeC m))
    (@♭ KXY : Closed (WholeB m × WholeC m))
    (@♭ law : ProductStatement.ProductAxiom KX KY KXY)
    → StagedProduct m

module ProductField {@♭ ℓ : Level} {@♭ m : DiagramMeta ℓ} where

  KX : (@♭ p : StagedProduct m) → Closed (WholeB m)
  KX (staged-product KX _ _ _) = KX

  KY : (@♭ p : StagedProduct m) → Closed (WholeC m)
  KY (staged-product _ KY _ _) = KY

  KXY : (@♭ p : StagedProduct m) → Closed (WholeB m × WholeC m)
  KXY (staged-product _ _ KXY _) = KXY

  law : (@♭ p : StagedProduct m)
      → ProductStatement.ProductAxiom (KX p) (KY p) (KXY p)
  law (staged-product _ _ _ law) = law

module Link
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ d : CapturedDiagram ℓ)
  (@♭ p : StagedProduct (metadata d)) where

  private
    module P = ProductField

  X Y : Set ℓ
  X = WholeB (metadata d)
  Y = WholeC (metadata d)

  -- The staged closed choices.
  sX : ShapeData X
  sX = closed-bridge fe X (P.KX p)

  sY : ShapeData Y
  sY = closed-bridge fe Y (P.KY p)

  sXY : ShapeData (X × Y)
  sXY = closed-bridge fe (X × Y) (P.KXY p)

  staged-law : PreservesProduct sX sY sXY
  staged-law =
    ProductStatement.preserves (P.KX p) (P.KY p) (P.KXY p) fe (P.law p)

  -- The whole shape data of the direct route: derived from the two
  -- captures that the bundle was made with, inside its context.
  tX : ShapeData X
  tX = AssembleCaptured.derivedB fe d

  tY : ShapeData Y
  tY = AssembleCaptured.derivedC fe d

  tXY : ShapeData (X × Y)
  tXY = sXY

  whole-product : PreservesProduct tX tY tXY
  whole-product =
    ProductChoice.transport-product sX tX sY tY sXY tXY staged-law
