{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The STAGED ROUTE on the dependent Bool/Code diagram. Claude (Fable),
-- 13 November 2026; after fable-impl-14 (HANDOFF-31;
-- S3-METADATA-STAGING-PREFLIGHT-01 section 4;
-- DIRECT-CAPTURE-GLOBAL-AXIOM-STAGING-01 section 6). BASIC theory: the
-- Nullstellensatz part is StagedDiagramPoints.
--
-- The diagram is the one of AssemblyClientGenerated, stated natively
-- ONCE, inside the context (b : Bool) (v : Code b). Nothing of it is
-- written a second time below: not the packed context, not a packed base,
-- map or family, not a source map, not a point.
--
--   1. in the context     the bundle and its descriptor, one declaration
--   2. empty context      the index, read from the NAME of the descriptor
--   3. empty context      three closed shapes and the product statement
--                         for the two whole sources of the index, through
--                         the existing entry points
--   4. in the context     the link: the product law for the whole shape
--                         data that the direct route derives
--
-- DECLARATIONS OF THIS FILE.
--   contextual (step 1): two shapes, requested by the one generator call;
--     choices at (b , v), of arity two (contextual-count).
--   global (step 3): three shapes in the empty context (global-count) and
--     ONE product statement. They are new choices and a new axiom about
--     closed types. None of them is a contextual choice moved or renamed,
--     and step 1 does not depend on them.
-- The reader (step 2) declares one definition and no axiom.
module StagedDiagramClient where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureContext using (CrispΣ; pair; CrispUnitAt; end-at)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalDeclare
open import BoolDecidable using (bool-dec)
open import DependentContextFixtures using (Code; code-dec)
open import DependentDiagramFixtures
open import DiagramBundle
open import DiagramMetadata
open import DeclareCapturedDiagram
open import ReadCapturedDiagram
open import StagedLink
open import DiagramInventory using (shape-axioms)

------------------------------------------------------------------------
-- 1. In the context. USER: the diagram, natively, once; two names.

module Local (@♭ b : Bool) (@♭ v : Code b) where

  unquoteDecl cells descriptor =
    declareStagedDiagram cells descriptor (bool-dec ∷ code-dec b ∷ [])
      (baseB-discrete b v) (baseB-set b v)
      (baseC-discrete b v) (baseC-set b v)
      (baseMap b v) (Fam b v)

  -- The descriptor is a view of the registered bundle: same point, same
  -- payloads, same two wrappers.
  same-bundle : bundle descriptor ≡ cells
  same-bundle = refl

  captured-B : CapturedShape (Σ (BaseB b v) (Fam b v))
  captured-B = CapturedField.localB (bundle descriptor)

  captured-C : CapturedShape (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  captured-C = CapturedField.localC (bundle descriptor)

  contextual-count : shape-axioms [] (quote captured-B ∷ quote captured-C ∷ []) ≡ 2
  contextual-count = refl

------------------------------------------------------------------------
-- 2. In the empty context. USER: one line. The descriptor is named, not
-- applied.

unquoteDecl index = readCapturedDiagram index (quote Local.descriptor)

index-type : DiagramMeta lzero
index-type = index

-- What the reader has had Agda check, stated natively: the descriptor,
-- unapplied, at the declared index, with its real binders.
linked : CrispPi Bool (λ b → CrispPi (Code b) (λ v → CapturedDiagramFor index))
linked = Local.descriptor

-- The index against the native data, at FORMAL variables. No point of
-- the context is chosen.
context-is : MetaField.G index
           ≡ CrispΣ Bool (λ b → CrispΣ (Code b) (λ _ → CrispUnitAt lzero))
context-is = refl

module _ (@♭ b : Bool) (@♭ v : Code b) where

  private
    here : MetaField.G index
    here = pair b (pair v end-at)

  base-B : MetaField.B index here ≡ BaseB b v
  base-B = refl

  base-C : MetaField.C index here ≡ BaseC b v
  base-C = refl

  -- The map, on its own.
  map-is : MetaField.f index here ≡ baseMap b v
  map-is = refl

  family-is : FibreAt (MetaField.A index) here ≡ Fam b v
  family-is = refl

  evidence-B : MetaField.dB index here ≡ baseB-discrete b v
  evidence-B = refl

  sets-C : MetaField.C-set index here ≡ baseC-set b v
  sets-C = refl

  -- The two local total sources.
  source-B : LocalTotal (MetaField.B index) (MetaField.A index) here
           ≡ Σ (BaseB b v) (Fam b v)
  source-B = refl

  source-C : LocalTotal (MetaField.C index)
               (Reindexed (MetaField.f index) (MetaField.A index)) here
           ≡ Σ (BaseC b v) (λ k → Fam b v (baseMap b v k))
  source-C = refl

  -- The index is the metadata of the bundle at these variables.
  same-metadata : metadata (Local.cells b v) ≡ index
  same-metadata = refl

------------------------------------------------------------------------
-- 3. In the empty context. USER: the staging, through the EXISTING entry
-- points. The two whole sources are stated from the index.

X Y : Set
X = WholeB index
Y = WholeC index

sX : CapturedShape X
sX = shape

sY : CapturedShape Y
sY = shape

sXY : CapturedShape (X × Y)
sXY = shape

KX : Closed X
KX = C.Output.whole-context sX

KY : Closed Y
KY = C.Output.whole-context sY

KXY : Closed (X × Y)
KXY = C.Output.whole-context sXY

unquoteDecl product = declareProduct product KX KY KXY

-- A package for the candidate `index`. Its type does not mention Local.
package : StagedProduct index
package = staged-product KX KY KXY product

global-count : shape-axioms [] (quote sX ∷ quote sY ∷ quote sXY ∷ []) ≡ 3
global-count = refl

------------------------------------------------------------------------
-- 4. In the context again, after function extensionality. USER: one line.

module Use (@♭ b : Bool) (@♭ v : Code b) (@♭ fe : FunExtAt lzero) where

  open Local b v

  -- Agda checks here that `package` is a package for the metadata of
  -- this bundle.
  module L = Link fe cells package

  whole-product : PreservesProduct L.tX L.tY L.tXY
  whole-product = L.whole-product

  -- tX and tY are the whole shape data of the direct route, derived from
  -- the two contextual captures; tXY is the staged closed choice.
  direct-B : L.tX ≡ AssembleCaptured.derivedB fe cells
  direct-B = refl

  direct-C : L.tY ≡ AssembleCaptured.derivedC fe cells
  direct-C = refl

  -- The comparison is the canonical one of these three shape data: on a
  -- unit it is the pair of units.
  on-units : (x : L.X) (y : L.Y)
           → compare L.tX L.tY L.tXY (η L.tXY (x , y)) ≡ (η L.tX x , η L.tY y)
  on-units = compare-η L.tX L.tY L.tXY

  -- Fed by the closed axiom and crisp data only, the law is usable
  -- crisply.
  crisp-use : ♭ (PreservesProduct L.tX L.tY L.tXY)
  crisp-use = box L.whole-product
