{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Decidable equality as DATA: the empty type, a decision of a type, and a
-- decision procedure for equality. Claude (Fable), 13 November 2026; step
-- S3c, after fable-impl-13 (HANDOFF-29, Q4; S3C-CAPTURED-DATA-DEPENDENCY-
-- SEAM-01). Postulate-free; no reflection; it imports Foundations only.
--
-- These ten lines are the declarations of DecidableBase (fable-impl-02),
-- moved here unchanged. DecidableBase re-exports them, so every earlier
-- import still finds them under the same names, and there is ONE
-- definition of each. They are separate because the data of a captured
-- diagram bundle (DiagramData) store a decision procedure for the packed
-- context, and DiagramData lies below the capture frontend: it must not
-- import the elimination and choice proofs of DecidableBase.
--
-- The quantifiers of DecEq are ordinary. That a bundle stores a procedure
-- crisply does not make its two arguments crisp.
module DecidableData where

open import Foundations

data ⊥ : Set where

absurd : ∀ {a} {A : Set a} → ⊥ → A
absurd ()

data Dec {a} (P : Set a) : Set a where
  yes : P → Dec P
  no : (P → ⊥) → Dec P

DecEq : ∀ {a} → Set a → Set a
DecEq A = (x y : A) → Dec (x ≡ y)
