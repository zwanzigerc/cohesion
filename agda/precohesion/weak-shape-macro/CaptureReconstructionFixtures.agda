{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Imported fixtures for CaptureReconstruction. They restate, under other
-- names, the fixtures of Astra's reconstruction-probes/src/ProbeFixtures.agda
-- (12 November 2026). The constants must be IMPORTED by the test: the
-- defect of Agda 2.9.0-rc3 is reached through the types of imported
-- constants and through clauses shorter than their uses.
-- Added by fable-impl-01; see FABLE-IMPL-01.txt.
module CaptureReconstructionFixtures where

open import Foundations
open import CaptureDroppedFixtures public using (Packed; package; Carrier; short; full; twice)

postulate
  k₀ : Packed ⊤
  x₀ : Carrier k₀
  -- A constant whose TYPE contains the over-applied form. Agda reconstructs
  -- this type when it reconstructs the parameters of `Carrier z₀`.
  z₀ : Packed (short k₀ x₀ ≡ short k₀ x₀)

-- A record without eta. A function matching on it is projection-like but
-- is not a proper projection, so its clause can be shorter than its uses.
record NoEtaEndo (A : Set) : Set where
  no-eta-equality
  pattern
  constructor noeta
  field run : A → A

bad : {A : Set} → NoEtaEndo A → A → A
bad (noeta f) = f

-- Projection-like functions whose PRINCIPAL BINDER is crisp. For these the
-- probe has to be reveal♭; an ordinary reveal does not type-check.
-- (fable-impl-02: FRONTEND-M1-AUDIT-01.txt §7 asked for this fixture. The
-- M1 test called CrispPrincipal had a crisp variable in an ordinary domain.)
crisp-carrier : {@♭ Γ : Set} (@♭ k : Packed Γ) → Set
crisp-carrier (package S _) = S

crisp-short : {@♭ Γ : Set} (@♭ k : Packed Γ) → crisp-carrier k → Γ
crisp-short (package _ f) = f

record EtaEndo (A : Set) : Set where
  constructor eta
  field run : A → A

good : {A : Set} → EtaEndo A → A → A
good (eta f) = f

postulate
  A₀ : Set
  r₀ : NoEtaEndo A₀
  e₀ : EtaEndo A₀
  a₀ : A₀
