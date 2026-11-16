{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Large elimination in use, as a hypothesis. fable-impl-02.
-- No axiom is declared here beyond the two captures themselves.
module LargeEliminationExamples where

open import Foundations
open import CaptureContext using (Raise; raise; lower)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge)
open import LargeElimination
open import GlobalDeclareExamples using (Space₁; K₁)

-- An independent capture of the same closed type, raised one universe.
-- Its carrier lives in Set₁ and has its universal property against the
-- discrete sets of Set₁.
raised : CapturedShape (Raise (lsuc lzero) Space₁)
raised = shape

K↑ : Closed (Raise (lsuc lzero) Space₁)
K↑ = C.Output.whole-context raised

module WithFunExt (@♭ fe₀ : FunExtAt lzero) (@♭ fe₁ : FunExtAt (lsuc lzero)) where

  small : ShapeData Space₁
  small = closed-bridge fe₀ Space₁ K₁

  big : ShapeData (Raise (lsuc lzero) Space₁)
  big = closed-bridge fe₁ (Raise (lsuc lzero) Space₁) K↑

  -- Always available: from the large choice to the raised small one,
  -- compatibly with the units.
  to-small : ʃ big → Raise (lsuc lzero) (ʃ small)
  to-small = Raised.forward (lsuc lzero) small big

  to-small-on-units : (x : Space₁)
    → to-small (η big (raise x)) ≡ raise (η small x)
  to-small-on-units x = Raised.forward-η (lsuc lzero) small big (raise x)

  -- With large elimination for the small choice, the two agree.
  module WithLarge (@♭ up : LargeFor (lsuc lzero) small) where

    agree : IsEquiv to-small
    agree = Compare.forward-is-equiv (lsuc lzero) small up big

    -- The map that the two-level principal-filter argument needs: from the
    -- shape of a small type to the shape of a large one.
    into-big : ʃ small → ʃ big
    into-big = Map.map↑ (lsuc lzero) small up big raise

    into-big-on-units : (x : Space₁) → into-big (η small x) ≡ η big (raise x)
    into-big-on-units = Map.map↑-η (lsuc lzero) small up big raise
