{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The staged route for two diagrams that differ ONLY in their map.
-- Claude (Fable), 13 November 2026; after fable-impl-14 (HANDOFF-31: the
-- full relevant index, f included when the family is constant). BASIC
-- theory.
--
-- The family is constant, so the map does not occur in the value of
-- either local total source: at every formal point the C-side sources of
-- the two diagrams are one type (one-source). The two indices are
-- nevertheless different terms, because the map is a field of the
-- metadata (maps-differ). So each descriptor has its own index, and a
-- package staged for one diagram is a package for that diagram.
-- StagedIndexOtherMap and StagedLinkOtherPackage are the two refusals.
--
-- DECLARATIONS OF THIS FILE.
--   contextual: one shape. The four requests of the two generator calls
--     are for one source in one context (contextual-count).
--   global: for the diagram with the map `collapse`, shapes for its two
--     whole sources and their product (global-count), and one product
--     statement. Nothing is staged for the other diagram.
module StagedDiagramMaps where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.List using (List; []; _∷_)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureContext using (pair; end-at)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalDeclare
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)
open import AssemblyFixtures using (keep; collapse; Constant)
open import DiagramBundle
open import DiagramMetadata
open import DeclareCapturedDiagram
open import ReadCapturedDiagram
open import StagedLink
open import DiagramInventory using (shape-axioms)

module Maps (@♭ b : Bool) where

  unquoteDecl kept kept-descriptor =
    declareStagedDiagram kept kept-descriptor (bool-dec ∷ [])
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set keep Constant

  unquoteDecl collapsed collapsed-descriptor =
    declareStagedDiagram collapsed collapsed-descriptor (bool-dec ∷ [])
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Constant

  private
    module F = CapturedField

  keptB : CapturedShape (Σ Bool Constant)
  keptB = F.localB kept

  keptC : CapturedShape (Σ Bool (λ x → Constant (keep x)))
  keptC = F.localC kept

  collapsedB : CapturedShape (Σ Bool Constant)
  collapsedB = F.localB collapsed

  collapsedC : CapturedShape (Σ Bool (λ x → Constant (collapse x)))
  collapsedC = F.localC collapsed

  contextual-count : shape-axioms []
      (quote keptB ∷ quote keptC ∷ quote collapsedB ∷ quote collapsedC ∷ []) ≡ 1
  contextual-count = refl

unquoteDecl kept-index = readCapturedDiagram kept-index (quote Maps.kept-descriptor)

unquoteDecl collapsed-index =
  readCapturedDiagram collapsed-index (quote Maps.collapsed-descriptor)

-- Each descriptor at its own index.
kept-linked : CrispPi Bool (λ b → CapturedDiagramFor kept-index)
kept-linked = Maps.kept-descriptor

collapsed-linked : CrispPi Bool (λ b → CapturedDiagramFor collapsed-index)
collapsed-linked = Maps.collapsed-descriptor

-- The two indices have different maps ...
maps-differ : MetaField.f kept-index (pair true end-at) true ≡ true
maps-differ = refl

maps-differ′ : MetaField.f collapsed-index (pair true end-at) true ≡ false
maps-differ′ = refl

-- ... and, at every formal point, one local total source on the C side:
-- the family is constant.
one-source : (@♭ b : Bool)
  → LocalTotal (MetaField.C kept-index)
      (Reindexed (MetaField.f kept-index) (MetaField.A kept-index)) (pair b end-at)
  ≡ LocalTotal (MetaField.C collapsed-index)
      (Reindexed (MetaField.f collapsed-index) (MetaField.A collapsed-index))
      (pair b end-at)
one-source b = refl

-- The B-side whole sources are one closed type.
one-whole-B : WholeB kept-index ≡ WholeB collapsed-index
one-whole-B = refl

-- Staging for the diagram with the map `collapse`.
sX : CapturedShape (WholeB collapsed-index)
sX = shape

sY : CapturedShape (WholeC collapsed-index)
sY = shape

sXY : CapturedShape (WholeB collapsed-index × WholeC collapsed-index)
sXY = shape

unquoteDecl product =
  declareProduct product (C.Output.whole-context sX) (C.Output.whole-context sY)
    (C.Output.whole-context sXY)

collapsed-package : StagedProduct collapsed-index
collapsed-package =
  staged-product (C.Output.whole-context sX) (C.Output.whole-context sY)
    (C.Output.whole-context sXY) product

global-count : shape-axioms [] (quote sX ∷ quote sY ∷ quote sXY ∷ []) ≡ 3
global-count = refl

-- The link for the diagram it was staged for.
module Use (@♭ b : Bool) (@♭ fe : FunExtAt lzero) where

  module L = Link fe (Maps.collapsed b) collapsed-package

  whole-product : PreservesProduct L.tX L.tY L.tXY
  whole-product = L.whole-product
