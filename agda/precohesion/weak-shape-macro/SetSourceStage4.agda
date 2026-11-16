{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE STAGED SET-SOURCE CLIENT, STAGE 4: the closed classifier. Choices
-- 11 to 13 of 21.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, sections 1.2 and 11.3 b).
--
-- DECLARATIONS OF THIS FILE: three shapes of level 2.
--   KOO   on ♯ (O 1) × ♯ (O 1)
--   KC    on ♯ C, C the closed carrier of the support
--   KLL   on L → L, L the carrier of the shape of ♯ C. Its source is
--         formed from the DECLARED KC, so it is staged after it.
module SetSourceStage4 where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; unit-at-discrete; unpack-unit-at; Raise)
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData; ʃ)
open import ClosedBridge using (module Bridge)
open import RelativeSliceShape
open import DeclareClosedShapeTyped
open import SetSourceStage3 public

------------------------------------------------------------------------
-- Choice 11: the square of ♯ (O 1).

T-OO : Set₂
T-OO = T-Oj × T-Oj

F-OO : CrispUnitAt ℓ₂ → Set₂
F-OO = unpack-unit-at (Raise ℓ₂ T-OO)

unquoteDecl KOO = declareClosedShapeTyped KOO
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-OO)

sOO : ShapeData T-OO
sOO = Bridge.data-of fe₂₂ T-OO KOO

------------------------------------------------------------------------
-- Choice 12: the sharp of the closed carrier.

T-C : Set₂
T-C = ♯ K2.C

F-C : CrispUnitAt ℓ₂ → Set₂
F-C = unpack-unit-at (Raise ℓ₂ T-C)

unquoteDecl KC = declareClosedShapeTyped KC
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-C)

sC : ShapeData T-C
sC = Bridge.data-of fe₂₂ T-C KC

------------------------------------------------------------------------
-- Choice 13: the endomaps of the carrier of that shape.

T-LL : Set₂
T-LL = ʃ sC → ʃ sC

F-LL : CrispUnitAt ℓ₂ → Set₂
F-LL = unpack-unit-at (Raise ℓ₂ T-LL)

unquoteDecl KLL = declareClosedShapeTyped KLL
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-LL)

sLL : ShapeData T-LL
sLL = Bridge.data-of fe₂₂ T-LL KLL

------------------------------------------------------------------------
-- The kernel's fourth module, at these closed data. DEFINED.

module K4 = K3.Classifier sOO sC sLL
