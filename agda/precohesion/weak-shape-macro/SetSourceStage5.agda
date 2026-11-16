{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE STAGED SET-SOURCE CLIENT, STAGE 5: the two attachments. Choices 14
-- to 21 of 21.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, sections 1.2, 1.4 and 11.3 b).
--
-- The default telescope: the attachments of the diagonals of the CLOSED
-- reflections cP WB and cP WC of the two whole bases, as agreed. (The
-- variant over the original bases, section 12.7 of the plan, is not
-- used.)
--
-- DECLARATIONS OF THIS FILE: eight shapes of level 2, four for each base.
--   KU      on the attachment U
--   KPow    on S → U,   S the carrier of the shape of U
--   KSecH   on S → ♭ U
--   KSecS   on S → S
-- The last three are formed from the DECLARED KU and are staged after it.
--
-- ORDINARY CONSTANTS IN THESE SOURCES. U is a quotient: its type contains
-- the quotient structures at 1 and 2 with their eliminators (through the
-- closed reflection and the truncations), and, through the proof that the
-- support is a proposition and through the false endpoint of the
-- classifier, function and propositional extensionality. All of them are
-- named constants of SetSourceFoundation. Up to conversion at most NINE
-- of the thirteen enter: Q₁, E₁, Q₂, E₂, fe₀₀, fe₁₁, fe₁₂, pe₀, pe₁;
-- effective₁, fe₂₂, fe₀₁ and truncation₀ do not (SetSourceSourceDependence,
-- sections 2, 4 and 5: checked with the data as variables). The
-- SYNTACTIC closure of each of these types reaches all thirteen, since a
-- module application passes every parameter.
module SetSourceStage5 where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; unit-at-discrete; unpack-unit-at; Raise)
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData; ʃ)
open import ClosedBridge using (module Bridge)
open import RelativeSliceShape
open import DeclareClosedShapeTyped
open import SetSourceStage4 public

------------------------------------------------------------------------
-- The attachment.

T-U : Set₂
T-U = K2.Att.U WB

F-U : CrispUnitAt ℓ₂ → Set₂
F-U = unpack-unit-at (Raise ℓ₂ T-U)

unquoteDecl KU = declareClosedShapeTyped KU
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-U)

sU : ShapeData T-U
sU = Bridge.data-of fe₂₂ T-U KU

------------------------------------------------------------------------
-- The power for the mere section.

T-Pow : Set₂
T-Pow = ʃ sU → T-U

F-Pow : CrispUnitAt ℓ₂ → Set₂
F-Pow = unpack-unit-at (Raise ℓ₂ T-Pow)

unquoteDecl KPow = declareClosedShapeTyped KPow
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-Pow)

sPow : ShapeData T-Pow
sPow = Bridge.data-of fe₂₂ T-Pow KPow

------------------------------------------------------------------------
-- The two powers that make the type of sections discrete.

T-SecH : Set₂
T-SecH = ʃ sU → ♭ T-U

F-SecH : CrispUnitAt ℓ₂ → Set₂
F-SecH = unpack-unit-at (Raise ℓ₂ T-SecH)

unquoteDecl KSecH = declareClosedShapeTyped KSecH
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-SecH)

sSecH : ShapeData T-SecH
sSecH = Bridge.data-of fe₂₂ T-SecH KSecH

------------------------------------------------------------------------
-- (continued)

T-SecS : Set₂
T-SecS = ʃ sU → ʃ sU

F-SecS : CrispUnitAt ℓ₂ → Set₂
F-SecS = unpack-unit-at (Raise ℓ₂ T-SecS)

unquoteDecl KSecS = declareClosedShapeTyped KSecS
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-SecS)

sSecS : ShapeData T-SecS
sSecS = Bridge.data-of fe₂₂ T-SecS KSecS

------------------------------------------------------------------------
-- The attachment of the second base.

T-U′ : Set₂
T-U′ = K2.Att.U WC

F-U′ : CrispUnitAt ℓ₂ → Set₂
F-U′ = unpack-unit-at (Raise ℓ₂ T-U′)

unquoteDecl KU′ = declareClosedShapeTyped KU′
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-U′)

sU′ : ShapeData T-U′
sU′ = Bridge.data-of fe₂₂ T-U′ KU′

------------------------------------------------------------------------
-- The power for the mere section of the second base.

T-Pow′ : Set₂
T-Pow′ = ʃ sU′ → T-U′

F-Pow′ : CrispUnitAt ℓ₂ → Set₂
F-Pow′ = unpack-unit-at (Raise ℓ₂ T-Pow′)

unquoteDecl KPow′ = declareClosedShapeTyped KPow′
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-Pow′)

sPow′ : ShapeData T-Pow′
sPow′ = Bridge.data-of fe₂₂ T-Pow′ KPow′

------------------------------------------------------------------------
-- The two powers that make the type of sections discrete of the second base.

T-SecH′ : Set₂
T-SecH′ = ʃ sU′ → ♭ T-U′

F-SecH′ : CrispUnitAt ℓ₂ → Set₂
F-SecH′ = unpack-unit-at (Raise ℓ₂ T-SecH′)

unquoteDecl KSecH′ = declareClosedShapeTyped KSecH′
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-SecH′)

sSecH′ : ShapeData T-SecH′
sSecH′ = Bridge.data-of fe₂₂ T-SecH′ KSecH′

------------------------------------------------------------------------
-- (continued)

T-SecS′ : Set₂
T-SecS′ = ʃ sU′ → ʃ sU′

F-SecS′ : CrispUnitAt ℓ₂ → Set₂
F-SecS′ = unpack-unit-at (Raise ℓ₂ T-SecS′)

unquoteDecl KSecS′ = declareClosedShapeTyped KSecS′
  (RelativeShapeOver (CrispUnitAt ℓ₂) unit-at-discrete F-SecS′)

sSecS′ : ShapeData T-SecS′
sSecS′ = Bridge.data-of fe₂₂ T-SecS′ KSecS′

------------------------------------------------------------------------
-- The kernel's last module, at these closed data. DEFINED.

module K5 = K4.Attachments sU sPow sSecH sSecS sU′ sPow′ sSecH′ sSecS′
