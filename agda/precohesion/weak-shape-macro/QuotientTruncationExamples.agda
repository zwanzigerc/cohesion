{-# OPTIONS --safe --without-K --cohesion #-}

-- Clients of the quotient interface and of the two truncations derived
-- from it. Claude (Fable), 14 November 2026; fable-impl-22 (HANDOFF-37,
-- items 1 and 2).
--
-- Literally --safe: this module and everything it imports. Nothing is
-- postulated: the quotient structure and its certificates are PARAMETERS
-- of every section. No instance of them exists in the tree.
--   1  both truncations from one structure; a set is its own set
--      truncation; the truncations compared; targets of the next level
--      through one further certificate
--   2  concrete levels zero and one
--   3  the crisp eliminator at the DERIVED truncation of a crisp
--      structure, and the boxed cover of a quotient map: every ordinary
--      point of ♭ (X / R) merely has a boxed representative
-- The refusal QuotientWrongTargetLevel.agda.fail shows that the property
-- at one level does not eliminate into another.
module QuotientTruncationExamples where

open import Foundations
open import SmallPropositions using (prop-is-set)
open import SharpPath using (FunExtAt)
open import OrdinaryTruncation
open import SmallQuotient
open import QuotientTruncations
import CrispTruncationExamples

------------------------------------------------------------------------
-- 1. One structure, both truncations.

module Derived {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ) where

  open FromQuotients Q E
  open PropTruncation prop-truncation
  open SetTruncation set-truncation

  -- The carriers stay at the level of the structure.
  carriers : Set ℓ → Set ℓ × Set ℓ
  carriers A = ∥ A ∥ , τ₀ A

  -- From the set truncation to the propositional one.
  to-prop : {A : Set ℓ} → τ₀ A → ∥ A ∥
  to-prop = τ₀-rec (prop-is-set squash) ∣_∣

  to-prop-unit : {A : Set ℓ} (a : A) → to-prop ∣ a ∣₀ ≡ ∣ a ∣
  to-prop-unit = τ₀-rec-unit (prop-is-set squash) ∣_∣

  -- For a set, the unit of the set truncation has a two-sided inverse.
  module OfASet {A : Set ℓ} (A-set : IsSet A) where

    back : τ₀ A → A
    back = τ₀-rec A-set (λ a → a)

    back-unit : (a : A) → back ∣ a ∣₀ ≡ a
    back-unit = τ₀-rec-unit A-set (λ a → a)

    unit-back : (z : τ₀ A) → ∣ back z ∣₀ ≡ z
    unit-back = τ₀-unique τ₀-set (λ z → ∣ back z ∣₀) (λ z → z)
      (λ a → ap ∣_∣₀ (back-unit a))

  -- Targets of the next level: one further certificate of the SAME
  -- structure gives both recursors there, on the same carriers.
  module Next (E⁺ : Eliminates Q (lsuc ℓ)) where

    prop-next : {A : Set ℓ} {P : Set (lsuc ℓ)} → IsProp P → (A → P)
              → ∥ A ∥ → P
    prop-next = prop-rec-into E⁺

    set-next : {A : Set ℓ} {D : Set (lsuc ℓ)} → IsSet D → (A → D)
             → τ₀ A → D
    set-next = SetRecInto.rec-into (set-truncation-into E⁺)

    set-next-unit : {A : Set ℓ} {D : Set (lsuc ℓ)} (D-set : IsSet D)
                  → (f : A → D) (a : A) → set-next D-set f ∣ a ∣₀ ≡ f a
    set-next-unit = SetRecInto.rec-into-unit (set-truncation-into E⁺)

------------------------------------------------------------------------
-- 2. Concrete levels.

module LevelZero (Q : Quotients lzero) (E : Eliminates Q lzero) where

  open FromQuotients Q E

  prop₀ : PropTruncation lzero
  prop₀ = prop-truncation

  set₀ : SetTruncation lzero
  set₀ = set-truncation

module LevelOne (Q : Quotients (lsuc lzero))
  (E : Eliminates Q (lsuc lzero))
  (E⁺ : Eliminates Q (lsuc (lsuc lzero))) where

  open FromQuotients Q E

  set₁ : SetTruncation (lsuc lzero)
  set₁ = set-truncation

  set₁-into-two : SetRecInto set₁ (lsuc (lsuc lzero))
  set₁-into-two = set-truncation-into E⁺

------------------------------------------------------------------------
-- 3. A crisp structure. Its derived truncation is a crisp term, so the
--    crisp eliminator applies to it; with the mere representatives of a
--    quotient map this gives the boxed cover of that map.

module CrispDerived {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Q : Quotients ℓ) (@♭ E : Eliminates Q ℓ) where

  open Quotients Q
  open FromQuotients Q E
  open PropTruncation prop-truncation

  private
    module Rep = Representatives Q E prop-truncation
    module Box = CrispTruncationExamples.Boxed fe prop-truncation

  class-cover : {@♭ X : Set ℓ} {@♭ R : EquivRel X} (v : ♭ (X / R))
              → ∥ Fiber (flat-map ([_] {R = R})) v ∥
  class-cover {X} {R} = Box.boxed-cover ([_] {R = R}) Rep.representative
