{-# OPTIONS --cohesion --without-K --flat-split #-}

-- An unfinished bundle is not a seed for itself. Claude (Fable),
-- 13 November 2026; generator checkpoint after fable-impl-11.
--
-- `self` is a HAND-WRITTEN bundle instance whose two payloads are
-- requested inside its own body. While that body is checked, `self` is
-- already an instance in scope. Whether the compiler hands it to the
-- lookup of CaptureReuse at that moment or filters it out earlier is not
-- traced here. If it is handed over, its two seeds cannot pass: the
-- sources and payloads of a bundle that has no clause yet do not reduce.
-- What the test checks is the endpoint: the two requests declare (two
-- axiom heads), the definition is not circular, and the file has no
-- unsolved meta.
--
-- The generator of DeclareDiagram never meets this case: it declares its
-- public name after both captures.
module DeclareDiagramSelf where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import AssemblyFixtures using (collapse; Colours)
open import DiagramData
open import DiagramInventory using (shape-axioms)

private
  the : ∀ {a} (A : Set a) → A → A
  the A x = x

instance
  self : ClosedDiagram lzero
  self = closed-diagram Bool Bool
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set
    collapse Colours
    (C.Output.whole-context (the (CapturedShape (Σ Bool Colours)) shape))
    (C.Output.whole-context (the (CapturedShape (Σ Bool (Colours ∘ collapse))) shape))

self-axioms : Nat
self-axioms = shape-axioms (quote self ∷ []) []

self-axioms-are : self-axioms ≡ 2
self-axioms-are = refl

-- Once complete, it is a seed like any other bundle.
afterwards : CapturedShape (Σ Bool Colours)
afterwards = shape

afterwards-same : afterwards ≡ ClosedSeed.seedB self
afterwards-same = refl
