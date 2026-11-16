{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE STAGED SET-SOURCE CLIENT, STAGE 3: the open part. Choices 7 to 10
-- of 21 and certificates 2 to 5 of 5.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, sections 1.2 and 11.3 b, c).
--
-- X and Y are the totals of the TRUNCATED payloads of stage 1, and
-- sX, sY their terminal shape data (TotalBridge.total-data: carrier and
-- unit those of MB, MC). They are DEFINED, so the certificates cX, cY on
-- them cannot be declared. Each is obtained as the staging document
-- says: an auxiliary closed shape on the SAME source, its declared
-- certificate, the comparison of the two shapes of that source
-- (GlobalChoice.Choice, an equivalence with its unit law), and
-- LargeTarget.Transfer with the mixed extensionality.
--
-- DECLARATIONS OF THIS FILE.
--   four choices of the kernel:    KaX, KaaX, KaY, KaaY     level 0
--   two certificates of the kernel: upaaX, upaaY           target level 1
--   AUXILIARY, not among the 21 + 5: the shapes KX, KY of X and Y and
--     their certificates upX, upY. They serve only to DERIVE cX and cY on
--     the carriers of the original payloads; the kernel never sees them.
module SetSourceStage3 where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; unit-at-discrete; unpack-unit-at; Raise)
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData)
open import GlobalChoice using (module Choice)
open import ClosedBridge using (module Bridge)
open import RelativeSliceShape
open import DeclareClosedShapeTyped
open import LargeTarget using (LargeOn; module Transfer)
open import LargeTargetDeclare using (declareLargeUP; attach)
open import SetSourceStage2 public

------------------------------------------------------------------------
-- ♯ ♭ X.

T-aX : Set
T-aX = ♯ (♭ K1.X)

F-aX : CrispUnitAt lzero → Set
F-aX = unpack-unit-at (Raise lzero T-aX)

unquoteDecl KaX = declareClosedShapeTyped KaX
  (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete F-aX)

saX : ShapeData T-aX
saX = Bridge.data-of fe₀₀ T-aX KaX

------------------------------------------------------------------------
-- Its square, with the certificate for the open diagonal.

T-aaX : Set
T-aaX = T-aX × T-aX

F-aaX : CrispUnitAt lzero → Set
F-aaX = unpack-unit-at (Raise lzero T-aaX)

unquoteDecl KaaX = declareClosedShapeTyped KaaX
  (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete F-aaX)

saaX : ShapeData T-aaX
saaX = Bridge.data-of fe₀₀ T-aaX KaaX

-- Certificate: sources of level 0, targets of level 1.

unquoteDecl upaaX = declareLargeUP upaaX ℓ₁ T-aaX KaaX

caaX : LargeOn ℓ₁ saaX
caaX = attach ℓ₁ T-aaX KaaX upaaX fe₀₀

------------------------------------------------------------------------
-- AUXILIARY: a closed shape of X itself, with its certificate.

T-X : Set
T-X = K1.X

F-X : CrispUnitAt lzero → Set
F-X = unpack-unit-at (Raise lzero T-X)

unquoteDecl KX = declareClosedShapeTyped KX
  (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete F-X)

sX : ShapeData T-X
sX = Bridge.data-of fe₀₀ T-X KX

unquoteDecl upX = declareLargeUP upX ℓ₁ T-X KX

-- The certificate on the shape of the PAYLOAD, transferred.
private
  module ChX = Choice sX K1.sX

cX : LargeOn ℓ₁ K1.sX
cX = Transfer.transfer ℓ₁ fe₀₁ ChX.forward ChX.forward-is-equiv
  ChX.forward-η (attach ℓ₁ T-X KX upX fe₀₀)

------------------------------------------------------------------------
-- ♯ ♭ Y.

T-aY : Set
T-aY = ♯ (♭ K1.Y)

F-aY : CrispUnitAt lzero → Set
F-aY = unpack-unit-at (Raise lzero T-aY)

unquoteDecl KaY = declareClosedShapeTyped KaY
  (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete F-aY)

saY : ShapeData T-aY
saY = Bridge.data-of fe₀₀ T-aY KaY

------------------------------------------------------------------------
-- Its square, with the certificate for the open diagonal.

T-aaY : Set
T-aaY = T-aY × T-aY

F-aaY : CrispUnitAt lzero → Set
F-aaY = unpack-unit-at (Raise lzero T-aaY)

unquoteDecl KaaY = declareClosedShapeTyped KaaY
  (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete F-aaY)

saaY : ShapeData T-aaY
saaY = Bridge.data-of fe₀₀ T-aaY KaaY

-- Certificate: sources of level 0, targets of level 1.

unquoteDecl upaaY = declareLargeUP upaaY ℓ₁ T-aaY KaaY

caaY : LargeOn ℓ₁ saaY
caaY = attach ℓ₁ T-aaY KaaY upaaY fe₀₀

------------------------------------------------------------------------
-- AUXILIARY: a closed shape of Y itself, with its certificate.

T-Y : Set
T-Y = K1.Y

F-Y : CrispUnitAt lzero → Set
F-Y = unpack-unit-at (Raise lzero T-Y)

unquoteDecl KY = declareClosedShapeTyped KY
  (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete F-Y)

sY : ShapeData T-Y
sY = Bridge.data-of fe₀₀ T-Y KY

unquoteDecl upY = declareLargeUP upY ℓ₁ T-Y KY

-- The certificate on the shape of the PAYLOAD, transferred.
private
  module ChY = Choice sY K1.sY

cY : LargeOn ℓ₁ K1.sY
cY = Transfer.transfer ℓ₁ fe₀₁ ChY.forward ChY.forward-is-equiv
  ChY.forward-η (attach ℓ₁ T-Y KY upY fe₀₀)

------------------------------------------------------------------------
-- The sources of this stage, written out. X and Y are the totals of the
-- TRUNCATED families over the two whole bases: of the ordinary constants
-- these types contain truncation₀ and no other.

X-is : K1.X ≡ Σ WB A₀
X-is = refl

Y-is : K1.Y ≡ Σ WC (A₀ ∘ wf)
Y-is = refl

------------------------------------------------------------------------
-- The kernel's third module, at these closed data. DEFINED.

module K3 = K2.Open saX saaX caaX cX saY saaY caaY cY
