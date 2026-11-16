{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Fixtures for the examples of the staged route. Claude (Fable),
-- 13 November 2026; after fable-impl-14. No postulate, no capture, no
-- reflection: definitions only. They are IMPORTED by the examples: the
-- pass that prepares a term for a capture refuses a definition of its own
-- file that does not unfold, and a decision procedure for an empty type
-- has no clause to unfold.
module StagedFixtures where

open import Foundations
open import Agda.Builtin.Bool
open import DecidableData using (⊥; DecEq)
open import DiagramData using (Presentation)

-- A decision procedure for the empty type.
empty-dec : DecEq ⊥
empty-dec ()

-- For StagedReaderCrispInside: a type of functions with a CRISP binder,
-- under a name, and the family of local total sources of a constant
-- family with that fibre over Bool. As names they are quoted as names;
-- written inline, their crisp binder is lost in reflected syntax.
CrispFunctions : Set
CrispFunctions = (@♭ x : Bool) → Bool

CrispTotals : Bool → Set
CrispTotals _ = Σ Bool (λ _ → CrispFunctions)

-- Every type presents itself.
itself : {X : Set} → Presentation X X
itself = (λ z → z) , (λ z → z) , (λ _ → refl) , (λ _ → refl)
