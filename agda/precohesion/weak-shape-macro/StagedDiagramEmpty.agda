{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The staged route over a context that has NO POINT. Claude (Fable),
-- 13 November 2026; after fable-impl-14 (S3-METADATA-STAGING-PREFLIGHT-01
-- section 4, second gate). BASIC theory.
--
-- The context is one crisp variable of the empty type ⊥: an ordinary
-- small type with a decision procedure, not an empty telescope. No
-- inhabitant of the packed context exists, so nothing below can depend on
-- one: the reader takes the NAME of the descriptor, and every statement
-- about the index is at a formal variable.
--
-- DECLARATIONS OF THIS FILE.
--   contextual: one shape, requested by the generator call under e : ⊥
--     (its two local sources are one type by conversion);
--   global: three shapes in the empty context and one product statement,
--     about the two whole sources of the index, which are empty types
--     (no-X, no-Y) and are not one type by conversion.
module StagedDiagramEmpty where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.List using (List; []; _∷_)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureContext using (CrispΣ; pair; CrispUnitAt; end-at)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalDeclare
open import DecidableData using (⊥)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import AssemblyFixtures using (keep; Colours)
open import StagedFixtures using (empty-dec)
open import DiagramBundle
open import DiagramMetadata
open import DeclareCapturedDiagram
open import ReadCapturedDiagram
open import StagedLink
open import DiagramInventory using (shape-axioms)

module Nowhere (@♭ e : ⊥) where

  unquoteDecl cells descriptor =
    declareStagedDiagram cells descriptor (empty-dec ∷ [])
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set keep Colours

  captured-B : CapturedShape (Σ Bool Colours)
  captured-B = CapturedField.localB cells

  captured-C : CapturedShape (Σ Bool (λ x → Colours (keep x)))
  captured-C = CapturedField.localC cells

  -- The two local sources are one type by conversion: one shape.
  contextual-count : shape-axioms [] (quote captured-B ∷ quote captured-C ∷ []) ≡ 1
  contextual-count = refl

unquoteDecl index = readCapturedDiagram index (quote Nowhere.descriptor)

linked : CrispPi ⊥ (λ e → CapturedDiagramFor index)
linked = Nowhere.descriptor

context-is : MetaField.G index ≡ CrispΣ ⊥ (λ _ → CrispUnitAt lzero)
context-is = refl

-- The packed context of the index has no point.
no-point : MetaField.G index → ⊥
no-point (pair e _) = e

-- The index against the native data, at a formal variable.
map-is : (@♭ e : ⊥) → MetaField.f index (pair e end-at) ≡ keep
map-is e = refl

family-is : (@♭ e : ⊥) → FibreAt (MetaField.A index) (pair e end-at) ≡ Colours
family-is e = refl

same-metadata : (@♭ e : ⊥) → metadata (Nowhere.cells e) ≡ index
same-metadata e = refl

-- Staging, through the existing entry points.
X Y : Set
X = WholeB index
Y = WholeC index

no-X : X → ⊥
no-X w = no-point (fst (fst w))

no-Y : Y → ⊥
no-Y w = no-point (fst (fst w))

sX : CapturedShape X
sX = shape

sY : CapturedShape Y
sY = shape

sXY : CapturedShape (X × Y)
sXY = shape

unquoteDecl product =
  declareProduct product (C.Output.whole-context sX) (C.Output.whole-context sY)
    (C.Output.whole-context sXY)

package : StagedProduct index
package = staged-product (C.Output.whole-context sX) (C.Output.whole-context sY)
  (C.Output.whole-context sXY) product

global-count : shape-axioms [] (quote sX ∷ quote sY ∷ quote sXY ∷ []) ≡ 3
global-count = refl

-- The link, under the variable of the empty type.
module Use (@♭ e : ⊥) (@♭ fe : FunExtAt lzero) where

  module L = Link fe (Nowhere.cells e) package

  whole-product : PreservesProduct L.tX L.tY L.tXY
  whole-product = L.whole-product
