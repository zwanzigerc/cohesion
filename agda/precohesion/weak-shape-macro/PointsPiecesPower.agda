{-# OPTIONS --cohesion --without-K --flat-split #-}

-- POINTS TO PIECES: the literal fibre of the power (Statement 4).
-- Opus, 13 November 2026; opus-points-pieces-01, implementing
-- POINTS-PIECES-SECTIONS-PLAN-FABLE-01.txt sections 3.2 and 4 step 6.
--
-- Under the hypotheses of Statement 1 (PointsPieces.Lifts) and one
-- ORDINARY same-level function extensionality hypothesis fe : FunExtAt ℓ,
--     merely-power-fiber : Merely (Fiber theta-power g),
-- where theta-power t w = points-to-pieces sX (t w). fe is used once, at the
-- function type W → ʃ sX, to turn the pointwise law of a lift into a path.
--
-- This is a SEPARATE file so that the extensionality hypothesis shows in
-- the import graph: a pointwise consumer of PointsPieces does not inherit
-- it. The kernel PointsPieces uses no extensionality.
--
-- Natively this is Merely of a fibre at each ordinary g. That it expresses
-- "θ^D is an epimorphism" in the base is a semantic reading (plan section
-- 9) and is not part of this module.
--
-- No postulate, macro or declaration. merely-map eliminates into the
-- caller's small proposition and needs no extensionality.
module PointsPiecesPower where

open import Foundations
open import GlobalPrecohesion
  using ( ShapeData; ʃ; ʃ-discrete; η; Merely
        ; points-to-pieces; Nullstellensatz; κ; κ-η; EpiC )
open import ShapeChoice using (FunExtAt)
open import GlobalPropositions using (merely-map)
open import PointsPieces using (module Lifts)

module Power
  {@♭ ℓ : Level} {@♭ X W : Set ℓ}
  (@♭ dW : Discrete W)
  (@♭ sX : ShapeData X)
  (@♭ sF : ShapeData (W → X)) where

  open Lifts dW sX sF using (merely-lift-points)

  theta-power : (W → ♭ X) → (W → ʃ sX)
  theta-power t w = points-to-pieces sX (t w)

  -- fe, ec, nF and g are all ordinary.
  merely-power-fiber : FunExtAt ℓ → EpiC dW sX sF → Nullstellensatz sF
                     → (g : W → ʃ sX) → Merely (Fiber theta-power g)
  merely-power-fiber fe ec nF g =
    merely-map (λ s → fst s , fe (snd s)) (merely-lift-points ec nF g)
