{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A bundle whose name is private. Claude (Fable), 13 November 2026;
-- generator checkpoint after fable-impl-11. Used by
-- DeclareDiagramOutOfScope: outside this module the instance `inner` is
-- not a name in scope, so no search finds it. `exported` is the same
-- value under a public name that is NOT an instance.
module DeclareDiagramPrivate where

open import Foundations
open import Agda.Builtin.Bool
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import AssemblyFixtures using (collapse; Colours)
open import DiagramData
open import DeclareDiagram using (declareClosedDiagram)

private
  unquoteDecl inner =
    declareClosedDiagram inner
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

exported : ClosedDiagram lzero
exported = inner
