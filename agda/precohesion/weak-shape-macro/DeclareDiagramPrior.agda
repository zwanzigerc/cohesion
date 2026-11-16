{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The reverse order: visible seeds first, the diagram afterwards. Claude
-- (Fable), 13 November 2026; generator checkpoint after fable-impl-11.
-- The generator's two requests go through the same lookup as `shape`, so
-- a registered choice of an eligible payload is used and no axiom is
-- declared for that side.
module DeclareDiagramPrior where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import DeclareCapturedShape using (declareShape)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import AssemblyFixtures using (collapse; keep; Colours)
open import DiagramData
open import DeclareDiagram using (declareClosedDiagram)
open import DiagramInventory using (shape-axioms)

-- 1. A seed for the B side only, registered by the delivered declaration.
unquoteDecl prior = declareShape prior (Σ Bool Colours)

unquoteDecl colours =
  declareClosedDiagram colours
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

prior-reused : ClosedField.KB colours ≡ C.Output.whole-context prior
prior-reused = refl

prior-wrapper : ClosedSeed.seedB colours ≡ prior
prior-wrapper = refl

-- One new axiom, for the C side.
one-new : Nat
one-new = shape-axioms (quote colours ∷ []) (quote prior ∷ [])

one-new-is : one-new ≡ 2
one-new-is = refl

-- 2. Both sides registered beforehand, the C side as a hand-written
-- instance: no new axiom.
instance
  prior-C : CapturedShape (Σ Bool (Colours ∘ collapse))
  prior-C = shape

unquoteDecl colours-later =
  declareClosedDiagram colours-later
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

-- prior-C was requested after `colours` and reused its C side.
prior-C-is : C.Output.whole-context prior-C ≡ ClosedField.KC colours
prior-C-is = refl

none-new : Nat
none-new = shape-axioms (quote colours ∷ quote colours-later ∷ [])
  (quote prior ∷ quote prior-C ∷ [])

none-new-is : none-new ≡ 2
none-new-is = refl

later-is-earlier : colours-later ≡ colours
later-is-earlier = refl
