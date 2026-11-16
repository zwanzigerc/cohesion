{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Instantiating an L0 (--safe) theorem from shape data. fable-impl-02.
--
-- precohesion-shape0/SafeProductNullstellensatz.agda is checked with --safe
-- and knows nothing of this tree. Here its parameters are filled from
-- ShapeData, and its conclusion is the theorem of GlobalPrecohesion with the
-- same statement, definitionally. This file is not --safe and makes no such
-- claim: it is where the trust levels meet.
module SafeConsumerExamples where

open import Foundations
open import GlobalPrecohesion
import SafeProductNullstellensatz as Safe

module _ {@♭ ℓ : Level} {@♭ X Y : Set ℓ}
  (@♭ sX : ShapeData X) (@♭ sY : ShapeData Y) (@♭ sXY : ShapeData (X × Y)) where

  private
    module S = Safe X Y (ʃ sX) (ʃ sY) (ʃ sXY) (η sX) (η sY) (η sXY)
      (first sX sY sXY) (second sX sY sXY)
      (rec-η sXY (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ p → η sX (fst p)))
      (rec-η sXY (ʃ sY) (ʃ-set sY) (ʃ-discrete sY) (λ p → η sY (snd p)))

  via-safe : PreservesProduct sX sY sXY
           → Nullstellensatz sX → Nullstellensatz sY → Nullstellensatz sXY
  via-safe = S.product-nullstellensatz
