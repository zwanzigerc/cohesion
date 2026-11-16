{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The mixed-level map of the bounded classifier argument, and its
-- naturality. Claude (Fable), 13 November 2026; fable-impl-03.
-- HANDOFF-06 item 5; CLASSIFIER-LARGE-UP-M1-AUDIT-02.txt section 4;
-- CLASSIFIER-UNIVERSE-REVIEW-01.txt (option B of FABLE-REVIEW-02 section 8).
-- Nothing is postulated or declared here.
--
-- For a level i:
--   Ω i        = Σ (Set i) IsProp            the propositions of level i,
--                                            a type of Set (lsuc i);
--   F          = { q : Ω i | unit q ≡ unit ⊤ }   the propositions that
--                T = shape ∘ ♯ identifies with truth, for a SELECTED
--                carrier SΩ and unit ηΩ of the shape of ♯ (Ω i);
--   ∀F φ       = (q : F) → El (φ q)          a proposition of level lsuc i,
--                                            for φ : F → Ω i.
-- So ∀F : (F → Ω i) → Ω (lsuc i) goes from a type of Set (lsuc i) to a
-- type of Set (lsuc (lsuc i)). T(∀F) needs the shape of ♯ (F → Ω i), a
-- SMALL carrier in Set (lsuc i), to map into the shape of ♯ (Ω (lsuc i)),
-- a discrete set one universe higher. That is what a certificate at
-- ceiling lsuc (lsuc i) for the small carrier provides, and what ShapeData
-- at level lsuc i does not.
--
-- This module is the map and its naturality square. It is not the
-- principal-filter theorem: the two halves of that argument, the base
-- classifier's discreteness, and the quotients it uses are not here.
-- The only extensionality is the one in the definition of ∀F (a product of
-- propositions is a proposition): FunExt₂ (lsuc i) i. The shape side uses
-- none.
module LargeTargetClassifier where

open import Foundations
open import CaptureContext using (Raise; raise)
open import NativeSharp using (♯; sharp-unit)
open import GlobalPropositions using (FunExt₂)
open import LargeTarget using (LargeTerminalUP; module SharpComposite)

Ω : (i : Level) → Set (lsuc i)
Ω i = Σ (Set i) IsProp

El : ∀ {i} → Ω i → Set i
El = fst

module _ {@♭ i : Level} where

  private
    one : IsProp (Raise i ⊤)
    one (raise tt) (raise tt) = refl

  -- Truth, at level i.
  ⊤Ω : Ω i
  ⊤Ω = Raise i ⊤ , one

  module TopClass (@♭ SΩ : Set (lsuc i)) (@♭ ηΩ : ♯ (Ω i) → SΩ) where

    unit-Ω : Ω i → SΩ
    unit-Ω q = ηΩ (sharp-unit q)

    F : Set (lsuc i)
    F = Σ (Ω i) (λ q → unit-Ω q ≡ unit-Ω ⊤Ω)

    ∀F : FunExt₂ (lsuc i) i → (F → Ω i) → Ω (lsuc i)
    ∀F fe φ = ((q : F) → El (φ q)) , λ u v → fe (λ q → snd (φ q) (u q) (v q))

    -- T(∀F), for a selected small shape of ♯ (F → Ω i) with a certificate
    -- at ceiling lsuc (lsuc i), and a selected shape of ♯ (Ω (lsuc i)).
    module Natural
      (@♭ SA : Set (lsuc i)) (@♭ ηA : ♯ (F → Ω i) → SA)
      (@♭ c : LargeTerminalUP (lsuc (lsuc i)) (♯ (F → Ω i)) SA ηA)
      (@♭ SB : Set (lsuc (lsuc i))) (@♭ SB-set : IsSet SB)
      (@♭ SB-discrete : Discrete SB) (@♭ ηB : ♯ (Ω (lsuc i)) → SB)
      (@♭ fe : FunExt₂ (lsuc i) i) where

      private
        module SC = SharpComposite (lsuc (lsuc i)) c SB SB-set SB-discrete ηB (∀F fe)

      T∀ : SA → SB
      T∀ = SC.T-map

      -- T(∀F) ∘ unit = unit ∘ ∀F : the equation that carries the
      -- mono-continuity equality at (Ω i, F) to the larger top class.
      T∀-natural : (φ : F → Ω i)
                 → T∀ (ηA (sharp-unit φ)) ≡ ηB (sharp-unit (∀F fe φ))
      T∀-natural = SC.T-natural
