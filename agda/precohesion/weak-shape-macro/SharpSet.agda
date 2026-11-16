{-# OPTIONS --safe --without-K --cohesion #-}

-- SET-SOURCE STAGE C4: native sharp preserves sets, at every level.
-- Opus, 14 November 2026; opus-closed-limits-01 (delta 03), implementing
-- SET-SOURCE-PLAN-ASTRA-RELEASE-01 (C4) and FABLE-PLAN-SET-SOURCE-01
-- section 6.2 (recipe of CLOSED-INTERVAL-DIRECT-EXTRACTION-01 section 4).
--
--   sharp-prop : FunExtAt ℓ → IsProp A → IsProp (♯ A)
--   sharp-set  : FunExtAt ℓ → IsSet A → IsSet (♯ A)
--
-- For s t : ♯ A put E s t = ♯ (s .ε ≡ t .ε).
--   enc : s ≡ t → E s t      transport of the reflexive element (built
--                            inside the field);
--   dec : E s t → s ≡ t      ap sharp-unit INSIDE the field, then
--                            SharpPath.sharp-path-extract (the one use of
--                            the ordinary FunExtAt ℓ);
--   dec is constant          the two sharp identifications of s and t that
--                            two points of E s t give are identified by
--                            sharp-path at the ORDINARY type s ≡ t, the set
--                            path of A being computed inside the field (a
--                            generic lemma cannot be applied to E s t itself,
--                            whose type mentions fields of ordinary s, t);
--   so dec ∘ enc is constant and ♯ A is a set (SmallPropositions.collapsible-set).
-- No field of an ordinary sharp point is used outside a sharp field; no
-- crisp variable, no --flat-split, nothing postulated: literally --safe.
-- The hypothesis is SharpPath.FunExtAt ℓ, which a FunExt₂ ℓ ℓ inhabits.
-- Use at the levels of the theorem (♯ C at k, ♯ (O i) at j) is by
-- instantiation; the lemma is generic.
module SharpSet where

open import Foundations
open import NativeSharp using (♯; ε; sharp-unit; transport)
open import SharpPath using (FunExtAt; sharp-path-extract)
open import SmallPropositions using (collapsible-set)

module _ {ℓ : Level} (fe : FunExtAt ℓ) where

  -- An identification of two sharp points from a sharp identification of
  -- their fields.
  sharp-path : {B : Set ℓ} (u v : ♯ B) → ♯ (u .ε ≡ v .ε) → u ≡ v
  sharp-path u v w = sharp-path-extract fe u v (λ where .ε → ap sharp-unit (w .ε))

module _ {ℓ : Level} (fe : FunExtAt ℓ) {A : Set ℓ} where

  sharp-prop : IsProp A → IsProp (♯ A)
  sharp-prop A-prop u v = sharp-path fe u v (λ where .ε → A-prop (u .ε) (v .ε))

  module _ (A-set : IsSet A) where

    E : ♯ A → ♯ A → Set ℓ
    E s t = ♯ (s .ε ≡ t .ε)

    enc : {s t : ♯ A} → s ≡ t → E s t
    enc {s} p = transport (E s) p (λ where .ε → refl)

    -- The sharp identification of s and t that a point of E s t gives.
    lift : {s t : ♯ A} → E s t → ♯ (s ≡ t)
    lift w = λ where .ε → ap sharp-unit (w .ε)

    dec : {s t : ♯ A} → E s t → s ≡ t
    dec {s} {t} w = sharp-path-extract fe s t (lift w)

    -- dec is constant. E s t mentions the fields of the ordinary s, t, so
    -- it cannot be handed to a generic lemma as an ordinary type; instead
    -- the two points lift w, lift w′ of the ORDINARY type ♯ (s ≡ t) are
    -- identified, by sharp-path at s ≡ t, with the set path of A computed
    -- inside the field.
    dec-constant : {s t : ♯ A} (w w′ : E s t) → dec w ≡ dec w′
    dec-constant {s} {t} w w′ = ap (sharp-path-extract fe s t)
      (sharp-path fe (lift w) (lift w′)
        (λ where .ε → ap (ap sharp-unit) (A-set (s .ε) (t .ε) (w .ε) (w′ .ε))))

    sharp-set : IsSet (♯ A)
    sharp-set = collapsible-set (λ p → dec (enc p))
      (λ p q → dec-constant (enc p) (enc q))

-- The exported form, with its hypotheses as arguments.
sharp-is-set : ∀ {ℓ} → FunExtAt ℓ → {A : Set ℓ} → IsSet A → IsSet (♯ A)
sharp-is-set fe A-set = sharp-set fe A-set
