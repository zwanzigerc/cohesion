{-# OPTIONS --cohesion --without-K --flat-split #-}

-- POINTS TO PIECES: MERE LIFTS AND MERE SECTIONS (the kernel).
-- Opus, 13 November 2026; opus-points-pieces-01, implementing
-- POINTS-PIECES-SECTIONS-PLAN-FABLE-01.txt sections 1, 3.1 and 4 (steps
-- 1-5) as released by POINTS-PIECES-PLAN-ASTRA-01.txt and
-- OPUS-POINTS-PIECES-RELEASE-01.txt.
--
-- Fix a crisp level ℓ, crisp X W : Set ℓ and crisp data
--     dW : Discrete W,   sX : ShapeData X,   sF : ShapeData (W → X).
-- With θ = points-to-pieces and κ = κ dW sX sF (the comparison of
-- GlobalPrecohesion, built from evaluation at crisp points):
--
--   Statement 2  points-power-square : θ sX (points-power u w) ≡ κ (θ sF u) w
--   Statement 1  merely-lift-points  : EpiC dW sX sF → Nullstellensatz sF
--                  → (g : W → ʃ sX) → Merely (LiftAlongPoints g)
--   Statement 3  merely-points-section : for sP : ShapeData (ʃ sX → X),
--                  EpiC (ʃ-discrete sX) sX sP → Nullstellensatz sP
--                  → Merely (PointsSection sX)
--   Statement 5  section-gives-points : Merely (PointsSection sX)
--                  → Nullstellensatz sX
-- (Statement 4, the literal fibre of the power, needs function
-- extensionality and is in the separate module PointsPiecesPower.)
--
-- Binders. Crisp: ℓ, X, W, dW, sX, sF / sP — forced by ♭, ShapeData, ʃ, η
-- and κ. ORDINARY: the EpiC witness, the Nullstellensatz witness, the map g,
-- the proposition P with its proof and continuation, both fibre witnesses,
-- and w. The only crisp function is the f exposed by matching `box f` on an
-- ordinary input; nothing ordinary is boxed or passed as a crisp map.
--
-- Merely is the bounded Church encoding of GlobalPrecohesion (elimination
-- into propositions of level ℓ only). Each proof first receives the small
-- proposition of its OUTER Merely and passes that same proposition through
-- every witness; there is no large elimination, no use of Merely being a
-- proposition, no function equality (the path from EpiC is consumed
-- pointwise by happly), no chosen witness.
--
-- What is NOT claimed. No section: the conclusion of Statement 3 is Merely
-- of the section type, not a section, a ♭ of one, or a crisp one. No
-- identification of Merely with a truncation or with base epimorphy (that
-- adequacy bridge is a separate theorem). Nothing about continuity: EpiC is
-- a hypothesis at one supplied discrete exponent W (the theorem's exponent
-- ʃ sX is a set by its field); no continuity axiom or schema. No
-- Nullstellensatz at X as a hypothesis — Statement 5 derives it. No shape
-- is formed here: the kernel only consumes supplied shape data and is not
-- the foundation endpoint for open-context capture.
--
-- Used: Foundations and the explicit list below from GlobalPrecohesion.
-- No function or proposition extensionality, product axiom, MonoC,
-- Continuous, choice, stability, truncation operation, large-target
-- certificate, macro or declaration. No postulate.
--
-- Flags: --flat-split is infective from GlobalPrecohesion, so it is kept
-- although the proof performs no crisp split (its one match on `box` is on
-- an ordinary argument). Not --safe while importing that foundation, and no
-- such claim.
module PointsPieces where

open import Foundations
open import GlobalPrecohesion
  using ( ShapeData; ʃ; ʃ-discrete; η; Merely
        ; points-to-pieces; Nullstellensatz; κ; κ-η; EpiC )

------------------------------------------------------------------------
-- Statements 1 and 2, for a supplied discrete exponent W.

module Lifts
  {@♭ ℓ : Level} {@♭ X W : Set ℓ}
  (@♭ dW : Discrete W)
  (@♭ sX : ShapeData X)
  (@♭ sF : ShapeData (W → X)) where

  -- A family of crisp points of X over W lifting g along points-to-pieces.
  LiftAlongPoints : (g : W → ʃ sX) → Set ℓ
  LiftAlongPoints g =
    Σ (W → ♭ X) (λ t → (w : W) → points-to-pieces sX (t w) ≡ g w)

  -- Step 1. f is crisp because it comes out of `box`; w stays ordinary and
  -- reaches ♭ W through the inverse of the counit of the discrete W.
  points-power : ♭ (W → X) → W → ♭ X
  points-power (box f) w = flat-map f (inverse dW w)

  -- Step 2 (Statement 2): the canonical square, ordinary in u and w.
  points-power-square : (u : ♭ (W → X)) (w : W)
                      → points-to-pieces sX (points-power u w)
                      ≡ κ dW sX sF (points-to-pieces sF u) w
  points-power-square (box f) w =
      ap (η sX) (flat-map-counit f (inverse dW w))
    ∙ ap (λ w′ → η sX (f w′)) (section dW w)
    ∙ sym (κ-η dW sX sF f w)

  -- Step 3 (Statement 1): mere lifts. ec, nF and g are ordinary.
  merely-lift-points : EpiC dW sX sF → Nullstellensatz sF
                     → (g : W → ʃ sX) → Merely (LiftAlongPoints g)
  merely-lift-points ec nF g P P-prop k =
    ec g P P-prop (λ a →
    nF (fst a) P P-prop (λ b →
    k ( points-power (fst b)
      , λ w → points-power-square (fst b) w
            ∙ ap (λ z′ → κ dW sX sF z′ w) (snd b)
            ∙ happly (snd a) w )))

------------------------------------------------------------------------
-- Statement 3: merely a section of points-to-pieces.

PointsSection : {@♭ ℓ : Level} {@♭ X : Set ℓ}
              → (@♭ sX : ShapeData X) → Set ℓ
PointsSection {X = X} sX =
  Σ (ʃ sX → ♭ X) (λ t → (z : ʃ sX) → points-to-pieces sX (t z) ≡ z)

-- Step 4: Statement 1 at W = ʃ sX, dW = ʃ-discrete sX, sF = sP, g = id.
-- The two Σ-types coincide definitionally; no shape is formed.
merely-points-section :
  {@♭ ℓ : Level} {@♭ X : Set ℓ}
  (@♭ sX : ShapeData X) (@♭ sP : ShapeData (ʃ sX → X))
  → EpiC (ʃ-discrete sX) sX sP → Nullstellensatz sP
  → Merely (PointsSection sX)
merely-points-section sX sP ec nP =
  Lifts.merely-lift-points (ʃ-discrete sX) sX sP ec nP (λ z → z)

------------------------------------------------------------------------
-- Statement 5: a mere section gives the Nullstellensatz at X, by
-- evaluation, still under the caller's small proposition.

section-gives-points :
  {@♭ ℓ : Level} {@♭ X : Set ℓ} (@♭ sX : ShapeData X)
  → Merely (PointsSection sX) → Nullstellensatz sX
section-gives-points sX m z P P-prop k =
  m P P-prop (λ s → k (fst s z , snd s z))
