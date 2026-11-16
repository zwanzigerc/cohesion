{-# OPTIONS --cohesion --without-K --flat-split #-}

-- POINTS TO PIECES: closed client and binder/level tests.
-- Opus, 13 November 2026; opus-points-pieces-01, implementing
-- POINTS-PIECES-SECTIONS-PLAN-FABLE-01.txt section 7. Every test below
-- applies the IMPLEMENTED exports of PointsPieces / PointsPiecesPower; no
-- statement-type stand-in is used.
--
-- 1. Closed client (plan 7.1). A postulated closed X₀ : Set; `shape` for
--    X₀; T₀ = the actual closed carrier of that capture, F₀ = T₀ → X₀;
--    `shape` for F₀; ONE Nullstellensatz declaration, for the shape of F₀
--    only. All of this is in the empty context, before fe is bound. Then,
--    in a module with the crisp fe : FunExtAt lzero that ClosedBridge needs,
--    the section and the Nullstellensatz at X₀ from an ORDINARY EpiC.
--
--    DIRECT DECLARATIONS of this file (see audit-probes for the reflection
--    inventory): the postulate X₀; two generated shape axioms, both
--    contextual-shape (0) (for X₀ and for F₀); one generated
--    Nullstellensatz axiom (NullstellensatzExtension, for KF). No product
--    axiom, no Nullstellensatz for KX, no continuity axiom: EpiC stays an
--    explicit ordinary hypothesis. fe is crisp because ClosedBridge asks for
--    it; the kernel PointsPieces does not see it.
--
-- 2. Ordinary binders (plan 7.2): the theorems applied to λ-bound ORDINARY
--    ec, nF / nP, g and (for the adapter) fe. Rejected if an implementation
--    strengthened any of them to crisp.
--
-- 3. Levels (plan 7.3): Lifts at level 1 and at the mixed instance (a
--    level-0 source explicitly raised beside a level-1 exponent).
--
-- 4. Definitional specialisation (plan step 4) and one use of a supplied
--    truncation (GlobalPropositions.to-truncation, unchanged).
module PointsPiecesExamples where

open import Foundations
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import CaptureContext using (Raise)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
  using ( ShapeData; ʃ; ʃ-discrete; Merely; Closed
        ; points-to-pieces; Nullstellensatz; κ; EpiC )
open import GlobalPropositions using (Truncation; to-truncation)
open import ClosedBridge using (closed-bridge; module Existence)
open import NullstellensatzExtension
  using (declareNullstellensatz; closed-nullstellensatz; module Statement)
open import PointsPieces
  using ( module Lifts; PointsSection; merely-points-section
        ; section-gives-points )
open import PointsPiecesPower using (module Power)

------------------------------------------------------------------------
-- 1. Closed client.

postulate X₀ : Set

captured-X : CapturedShape X₀
captured-X = shape

KX : Closed X₀
KX = C.Output.whole-context captured-X

T₀ : Set
T₀ = Existence.T X₀ KX

F₀ : Set
F₀ = T₀ → X₀

captured-F : CapturedShape F₀
captured-F = shape

KF : Closed F₀
KF = C.Output.whole-context captured-F

unquoteDecl points-F = declareNullstellensatz points-F KF

type-of-points-F : Statement.NAxiom KF
type-of-points-F = points-F

module Client (@♭ fe : FunExtAt lzero) where

  sX : ShapeData X₀
  sX = closed-bridge fe X₀ KX

  same-carrier : ʃ sX ≡ T₀
  same-carrier = refl

  sP : ShapeData (ʃ sX → X₀)
  sP = closed-bridge fe F₀ KF

  nP : Nullstellensatz sP
  nP = closed-nullstellensatz fe F₀ KF points-F

  -- Statement 3 at the closed client, from an ordinary EpiC.
  result : EpiC (ʃ-discrete sX) sX sP → Merely (PointsSection sX)
  result ec = merely-points-section sX sP ec nP

  -- Statement 5: hence the Nullstellensatz at X₀ (not assumed).
  points-at-X : EpiC (ʃ-discrete sX) sX sP → Nullstellensatz sX
  points-at-X ec = section-gives-points sX (result ec)

------------------------------------------------------------------------
-- 2. Ordinary binders, on the implemented theorems.

module OrdinaryUse
  {@♭ ℓ : Level} {@♭ X W : Set ℓ}
  (@♭ dW : Discrete W) (@♭ sX : ShapeData X) (@♭ sF : ShapeData (W → X))
  where
  open Lifts dW sX sF
  open Power dW sX sF

  lift-use : (ec : EpiC dW sX sF) (nF : Nullstellensatz sF) (g : W → ʃ sX)
           → Merely (LiftAlongPoints g)
  lift-use ec nF g = merely-lift-points ec nF g

  square-use : (u : ♭ (W → X)) (w : W)
             → points-to-pieces sX (points-power u w)
             ≡ κ dW sX sF (points-to-pieces sF u) w
  square-use u w = points-power-square u w

  power-use : (fe : FunExtAt ℓ) (ec : EpiC dW sX sF) (nF : Nullstellensatz sF)
              (g : W → ʃ sX) → Merely (Fiber theta-power g)
  power-use fe ec nF g = merely-power-fiber fe ec nF g

module OrdinarySection
  {@♭ ℓ : Level} {@♭ X : Set ℓ}
  (@♭ sX : ShapeData X) (@♭ sP : ShapeData (ʃ sX → X)) where

  section-use : (ec : EpiC (ʃ-discrete sX) sX sP) (nP : Nullstellensatz sP)
              → Merely (PointsSection sX)
  section-use ec nP = merely-points-section sX sP ec nP

  points-use : (m : Merely (PointsSection sX)) → Nullstellensatz sX
  points-use m = section-gives-points sX m

  -- Definitional specialisation: Statement 3's Σ-type is Statement 1's.
  specialisation : Lifts.LiftAlongPoints (ʃ-discrete sX) sX sP (λ z → z)
                 ≡ PointsSection sX
  specialisation = refl

  -- A supplied truncation at level ℓ applies to the result as it stands.
  module _ (t : Truncation ℓ) where
    open Truncation t using (∥_∥)

    truncated : EpiC (ʃ-discrete sX) sX sP → Nullstellensatz sP
              → ∥ PointsSection sX ∥
    truncated ec nP = to-truncation t (section-use ec nP)

------------------------------------------------------------------------
-- 3. Levels.

module AtLevelOne
  (@♭ X W : Set₁) (@♭ dW : Discrete W)
  (@♭ sX : ShapeData X) (@♭ sF : ShapeData (W → X)) where
  open Lifts dW sX sF

  lift-level : (g : W → ʃ sX) → Set₁
  lift-level = LiftAlongPoints

  theorem-at-level-one :
    EpiC dW sX sF → Nullstellensatz sF → (g : W → ʃ sX)
    → Merely (LiftAlongPoints g)
  theorem-at-level-one = merely-lift-points

  theorem-level : Set₂
  theorem-level = EpiC dW sX sF → Nullstellensatz sF
                → (g : W → ʃ sX) → Merely (LiftAlongPoints g)

  hypotheses-level : Set₂
  hypotheses-level = EpiC dW sX sF × Nullstellensatz sF

module Mixed
  (@♭ X : Set) (@♭ W : Set₁) (@♭ dW : Discrete W)
  (@♭ sX : ShapeData (Raise (lsuc lzero) X))
  (@♭ sF : ShapeData (W → Raise (lsuc lzero) X)) where
  open Lifts dW sX sF

  theorem-mixed :
    EpiC dW sX sF → Nullstellensatz sF → (g : W → ʃ sX)
    → Merely (LiftAlongPoints g)
  theorem-mixed = merely-lift-points

  lifts-are-points-of-the-raised-type :
    (g : W → ʃ sX) → LiftAlongPoints g → W → ♭ (Raise (lsuc lzero) X)
  lifts-are-points-of-the-raised-type g = fst
