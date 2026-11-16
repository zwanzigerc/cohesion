{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE STAGED SET-SOURCE CLIENT, STAGE 2: the support. Choices 2 to 6 of
-- 21 and certificate 1 of 5.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, sections 1.2 and 11.3 b).
--
-- The sources are formed from the shape sO of stage 1 alone
-- (PrincipalFilter.Principal sO): F, Q, P, R. So this stage can only
-- follow that declaration, and each source below is a closed type that
-- mentions the constant KO.
--
-- DECLARATIONS OF THIS FILE: five shapes and one larger-target
-- certificate, each a closed statement in the empty context.
--   KQ    on Q = F → O 0                 level 1
--   KR    on R = P → O 1                 level 2
--   KE    on F → ♯ (O 0)                 level 1
--   KYQ   on ♯ Q                         level 1
--   KOj   on ♯ (O 1)                     level 2
--   upQ   the universal property of KYQ against discrete sets of level 2
-- ORDINARY CONSTANTS IN THESE SOURCES. Q, R, F and P are formed from the
-- carrier and the unit of sO, before any extensionality (PrincipalFilter,
-- header). The defined shape datum sO = Bridge.data-of fe₁₁ T-O KO
-- mentions fe₁₁, so that NAME occurs in the sources formed from the
-- support; its carrier and unit, which are all that those sources use,
-- do not depend on it. The source ♯ (O 1) of KOj has none.
module SetSourceStage2 where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; unit-at-discrete; unpack-unit-at; Raise)
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData)
open import ClosedBridge using (module Bridge)
open import RelativeSliceShape
open import DeclareClosedShapeTyped
open import LargeTarget using (LargeOn)
open import LargeTargetDeclare using (declareLargeUP; attach)
open import BaseClassifier using (O)
open import SetSourceStage1 public

private
  module Pr = K1.Pr

------------------------------------------------------------------------
-- Choice 2: Q = F → O 0.

T-Q : Set₁
T-Q = Pr.Q

F-Q : CrispUnitAt ℓ₁ → Set₁
F-Q = unpack-unit-at (Raise ℓ₁ T-Q)

unquoteDecl KQ = declareClosedShapeTyped KQ
  (RelativeShapeOver (CrispUnitAt ℓ₁) unit-at-discrete F-Q)

sQ : ShapeData T-Q
sQ = Bridge.data-of fe₁₁ T-Q KQ

------------------------------------------------------------------------
-- Choice 3: R = P → O 1.

T-R : Set₂
T-R = Pr.R

F-R : CrispUnitAt ℓ₂ → Set₂
F-R = unpack-unit-at (Raise ℓ₂ T-R)

unquoteDecl KR = declareClosedShapeTyped KR
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-R)

sR : ShapeData T-R
sR = Bridge.data-of fe₂₂ T-R KR

------------------------------------------------------------------------
-- Choice 4: F → ♯ (O 0).

T-E : Set₁
T-E = Pr.F → ♯ (O lzero)

F-E : CrispUnitAt ℓ₁ → Set₁
F-E = unpack-unit-at (Raise ℓ₁ T-E)

unquoteDecl KE = declareClosedShapeTyped KE
  (RelativeShapeOver (CrispUnitAt ℓ₁) unit-at-discrete F-E)

sE : ShapeData T-E
sE = Bridge.data-of fe₁₁ T-E KE

------------------------------------------------------------------------
-- Choice 5: ♯ Q, and certificate 1: its universal property against the
-- discrete sets of level 2, on the SAME carrier and unit.

T-YQ : Set₁
T-YQ = ♯ Pr.Q

F-YQ : CrispUnitAt ℓ₁ → Set₁
F-YQ = unpack-unit-at (Raise ℓ₁ T-YQ)

unquoteDecl KYQ = declareClosedShapeTyped KYQ
  (RelativeShapeOver (CrispUnitAt ℓ₁) unit-at-discrete F-YQ)

sYQ : ShapeData T-YQ
sYQ = Bridge.data-of fe₁₁ T-YQ KYQ

unquoteDecl upQ = declareLargeUP upQ ℓ₂ T-YQ KYQ

cQ : LargeOn ℓ₂ sYQ
cQ = attach ℓ₂ T-YQ KYQ upQ fe₁₁

------------------------------------------------------------------------
-- Choice 6: ♯ (O 1).

T-Oj : Set₂
T-Oj = ♯ (O ℓ₁)

F-Oj : CrispUnitAt ℓ₂ → Set₂
F-Oj = unpack-unit-at (Raise ℓ₂ T-Oj)

unquoteDecl KOj = declareClosedShapeTyped KOj
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-Oj)

sOj : ShapeData T-Oj
sOj = Bridge.data-of fe₂₂ T-Oj KOj

------------------------------------------------------------------------
-- The kernel's second module, at these closed data. DEFINED.

module K2 = K1.Support sQ sR sE sYQ cQ sOj
