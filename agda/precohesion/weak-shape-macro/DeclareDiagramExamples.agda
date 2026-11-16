{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The closed-diagram generator and the registration of its choices.
-- Claude (Fable), 13 November 2026; generator checkpoint after
-- fable-impl-11. Every equality below is checked by reduction alone.
--
-- The acceptance statements of DIAGRAM-REUSE-DESIGN-OPTIONS-01 section 6
-- at top level: a repeated diagram, ordinary `shape` after a diagram,
-- coinciding sources within one call, shared shapes with distinct maps,
-- transparent aliases, unrelated visible diagrams. The reverse order (a
-- visible seed before the diagram) is DeclareDiagramPrior; reuse across
-- an import is DeclareDiagramImport; level one is in DeclareDiagramClient.
--
-- COUNTS are those of DiagramInventory: distinct axiom heads of the
-- listed payloads. Read with its header.
module DeclareDiagramExamples where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import DependentDiagramFixtures
  using (Row; Col; row-discrete; row-set; col-discrete; col-set; step; Cell)
open import AssemblyFixtures using (collapse; keep; Colours; Constant)
open import DiagramData
open import DeclareDiagram using (declareClosedDiagram)
open import DiagramInventory using (shape-axioms)
open import Agda.Builtin.List using ([]; _∷_)

------------------------------------------------------------------------
-- 1. One declaration. The user's side is this line.

unquoteDecl cells =
  declareClosedDiagram cells row-discrete row-set col-discrete col-set step Cell

-- The fields are the user's data.
cells-B : ClosedField.B cells ≡ Row
cells-B = refl

cells-map : ClosedField.f cells ≡ step
cells-map = refl

cells-family : ClosedField.A cells ≡ Cell
cells-family = refl

cells-evidence : ClosedField.dC cells ≡ col-discrete
cells-evidence = refl

-- Two distinct sources, no earlier seed: two axioms.
cells-axioms : Nat
cells-axioms = shape-axioms (quote cells ∷ []) []

cells-axioms-are : cells-axioms ≡ 2
cells-axioms-are = refl

------------------------------------------------------------------------
-- 2. The same diagram again: no new axiom, the same choices.

unquoteDecl cells-again =
  declareClosedDiagram cells-again row-discrete row-set col-discrete col-set step Cell

left-payload-same : ClosedField.KB cells ≡ ClosedField.KB cells-again
left-payload-same = refl

right-payload-same : ClosedField.KC cells ≡ ClosedField.KC cells-again
right-payload-same = refl

left-seed-same : ClosedSeed.seedB cells ≡ ClosedSeed.seedB cells-again
left-seed-same = refl

whole-bundle-same : cells ≡ cells-again
whole-bundle-same = refl

both-axioms : Nat
both-axioms = shape-axioms (quote cells ∷ quote cells-again ∷ []) []

both-axioms-are : both-axioms ≡ 2
both-axioms-are = refl

------------------------------------------------------------------------
-- 3. Ordinary shape requests after the diagram reuse its choices.

againB : CapturedShape (ClosedSeed.sourceB cells)
againB = shape

ordinary-repeat : C.Output.whole-context againB ≡ ClosedField.KB cells
ordinary-repeat = refl

ordinary-wrapper : againB ≡ ClosedSeed.seedB cells
ordinary-wrapper = refl

-- The same request in the user's own spelling of the source.
againC : CapturedShape (Σ Col (Cell ∘ step))
againC = shape

ordinary-repeat-C : C.Output.whole-context againC ≡ ClosedField.KC cells
ordinary-repeat-C = refl

ordinary-carrier : C.Output.carrier againC ≡ C.Output.carrier (ClosedSeed.seedC cells)
ordinary-carrier = refl

ordinary-unit : C.Output.unit againC ≡ C.Output.unit (ClosedSeed.seedC cells)
ordinary-unit = refl

-- A transparent alias of a source.
Alias : Set
Alias = Σ Row Cell

aliased : CapturedShape Alias
aliased = shape

aliased-same : C.Output.whole-context aliased ≡ ClosedField.KB cells
aliased-same = refl

with-ordinary : Nat
with-ordinary = shape-axioms (quote cells ∷ [])
  (quote againB ∷ quote againC ∷ quote aliased ∷ [])

with-ordinary-is : with-ordinary ≡ 2
with-ordinary-is = refl

------------------------------------------------------------------------
-- 4. Coinciding sources within ONE call: one axiom. keep is the identity
-- of Bool, so  Σ Bool (Colours ∘ keep)  is  Σ Bool Colours  by conversion,
-- and so are the two audited payloads.

unquoteDecl same =
  declareClosedDiagram same
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set keep Colours

same-source : ClosedField.KB same ≡ ClosedField.KC same
same-source = refl

same-axioms : Nat
same-axioms = shape-axioms (quote same ∷ []) []

same-axioms-are : same-axioms ≡ 1
same-axioms-are = refl

------------------------------------------------------------------------
-- 5. An unrelated diagram in between does not obstruct a later hit, and
-- one side of a new diagram can be an existing choice: collapse changes
-- the C side only.

unquoteDecl colours =
  declareClosedDiagram colours
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

shared-side : ClosedField.KB colours ≡ ClosedField.KB same
shared-side = refl

-- `same` has one axiom; `colours` adds exactly one, for its C side.
same-and-colours : Nat
same-and-colours = shape-axioms (quote same ∷ quote colours ∷ []) []

same-and-colours-are : same-and-colours ≡ 2
same-and-colours-are = refl

-- With cells, cells-again, same and colours all visible, a request for a
-- source of the first diagram still finds it.
late : CapturedShape (Σ Row Cell)
late = shape

late-same : late ≡ ClosedSeed.seedB cells
late-same = refl

------------------------------------------------------------------------
-- 6. Shapes shared, maps kept apart. Constant is a constant family, and
-- here both bases are Bool: for every map of Bool to itself the reindexed
-- total is  Σ Bool Constant  again by conversion, so both diagrams below
-- have one and the same source on both sides. They share one axiom.
-- (Constant fibres alone would not do that: over two different bases the
-- two totals are different types.) Their maps are the user's two maps.

unquoteDecl kept =
  declareClosedDiagram kept
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set keep Constant

unquoteDecl collapsed =
  declareClosedDiagram collapsed
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Constant

id-action : ClosedField.f kept true ≡ true
id-action = refl

const-action : ClosedField.f collapsed true ≡ false
const-action = refl

shared-shapes : ClosedField.KC kept ≡ ClosedField.KC collapsed
shared-shapes = refl

constant-axioms : Nat
constant-axioms = shape-axioms (quote kept ∷ quote collapsed ∷ []) []

constant-axioms-are : constant-axioms ≡ 1
constant-axioms-are = refl

-- That the two bundles are NOT identified is the negative test
-- DeclareDiagramMapsDiffer.agda.fail.

-- The generator's last step, written out by hand for `kept`: the direct
-- constructor `generated` checked at ClosedDiagramOf of the user's own
-- data. It is accepted for the map keep. For the map collapse the same
-- constructor term is refused, although the sources and payloads agree:
-- DeclareDiagramWrongMap.agda.fail.
kept-is-generated :
  ClosedDiagramOf bool-is-discrete bool-is-set bool-is-discrete bool-is-set
    keep Constant kept
kept-is-generated = generated (ClosedField.KB kept) (ClosedField.KC kept)

------------------------------------------------------------------------
-- 7. A module without parameters is not a context: the declaration is
-- accepted there, and finds the earlier bundle.

module Nested where

  unquoteDecl cells-nested =
    declareClosedDiagram cells-nested row-discrete row-set col-discrete col-set step Cell

  nested-same : cells-nested ≡ cells
  nested-same = refl

------------------------------------------------------------------------
-- 8. The whole file: seven declarations of diagrams, three ordinary
-- requests and one late request, five axioms.

all-axioms : Nat
all-axioms = shape-axioms
  (quote cells ∷ quote cells-again ∷ quote same ∷ quote colours
   ∷ quote kept ∷ quote collapsed ∷ quote Nested.cells-nested ∷ [])
  (quote againB ∷ quote againC ∷ quote aliased ∷ quote late ∷ [])

all-axioms-are : all-axioms ≡ 5
all-axioms-are = refl
