{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Imported fixtures for CaptureDroppedParameters and the CaptureOverApplied
-- rejection tests. Added 11 November 2026 (Fable); see FABLE-ADDITIONS.txt.
module CaptureDroppedFixtures where

open import Foundations

data Packed (Γ : Set) : Set₁ where
  package : (S : Set) → (S → Γ) → Packed Γ

-- Projection-like, applied to exactly the arguments its clause takes.
Carrier : {Γ : Set} → Packed Γ → Set
Carrier (package S _) = S

-- Projection-like on a data type, with a clause SHORTER than its uses.
-- Parameter reconstruction of `short k x` aborts Agda 2.9.0-rc3.
short : {Γ : Set} (k : Packed Γ) → Carrier k → Γ
short (package _ f) = f

-- The same function with every argument on the left-hand side.
full : {Γ : Set} (k : Packed Γ) → Carrier k → Γ
full (package _ f) x = f x

-- Projection-like without matching, again shorter than its uses.
-- `twice k x` aborts Agda 2.9.0-rc3 in the same way.
twice : {Γ : Set} (k : Packed Γ) → Carrier k → Γ
twice k = short k

-- The over-applied form behind a definition.
Wrapped : Packed ⊤ → Set
Wrapped k = (x : Carrier k) → short k x ≡ short k x

record Endo (A : Set) : Set where
  constructor endo
  field apply : A → A

-- Functions on a RECORD type with clauses shorter than their uses. These
-- do not trigger the regression.
rp : {A : Set} → Endo A → A → A
rp e = Endo.apply e

rq : {A : Set} → Endo A → A → A
rq (endo f) = f
