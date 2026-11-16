{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Reuse across an import. Claude (Fable), 13 November 2026; generator
-- checkpoint after fable-impl-11. The public bundles of
-- DeclareDiagramExamples are instances; their seed names are not in scope
-- anywhere. What is found is decided by the compiler's ordinary rule for
-- instances: a candidate must be a name in scope, and after `import M`
-- every public name of M is in scope under its qualified name, whether or
-- not it was opened. So a bundle of an imported module is found even when
-- the import's `using` list leaves it out. (The compiler's option
-- --no-qualified-instances narrows this to unqualified names; no file of
-- this tree sets it.) A bundle that is NOT in scope, here a private one,
-- is not found: DeclareDiagramPrivate, DeclareDiagramOutOfScope.
module DeclareDiagramImport where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import DependentDiagramFixtures
  using (Row; Col; row-discrete; row-set; col-discrete; col-set; step; Cell)
open import AssemblyFixtures using (collapse; Colours)
open import DiagramData
open import DeclareDiagram using (declareClosedDiagram)
open import DiagramInventory using (shape-axioms)
open import DeclareDiagramExamples using (cells)

-- An ordinary request for a source of the imported diagram.
imported-B : CapturedShape (Σ Row Cell)
imported-B = shape

imported-B-same : imported-B ≡ ClosedSeed.seedB cells
imported-B-same = refl

-- The generator, for the same diagram, in this file: no new axiom.
unquoteDecl cells-here =
  declareClosedDiagram cells-here row-discrete row-set col-discrete col-set step Cell

here-is-there : cells-here ≡ cells
here-is-there = refl

still-two : Nat
still-two = shape-axioms (quote cells ∷ quote cells-here ∷ []) (quote imported-B ∷ [])

still-two-are : still-two ≡ 2
still-two-are = refl

-- `colours` of DeclareDiagramExamples is not in the `using` list above.
-- It is in scope as DeclareDiagramExamples.colours, and that is enough.
unquoteDecl colours-here =
  declareClosedDiagram colours-here
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

qualified-reuse : colours-here ≡ DeclareDiagramExamples.colours
qualified-reuse = refl
