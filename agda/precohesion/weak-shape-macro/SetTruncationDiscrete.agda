{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The set truncation of a crisp discrete type is discrete.
-- Claude (Fable), 14 November 2026; fable-impl-23 (HANDOFF-38).
--
-- For a crisp SetTruncation τ and a crisp discrete H, the unit
-- h ↦ ∣ h ∣₀ lifts through the inverse of the counit of H to a map
-- H → ♭ (τ₀ H); it extends to τ₀ H because ♭ (τ₀ H) is a set
-- (NativeFlatIdentity.flat-set); the counit of the extension is the
-- identity on units, hence everywhere by uniqueness; then
-- DiscretePullback.counit-section-discrete. The same argument as
-- TruncationDiscrete of fable-impl-20 for the propositional truncation.
-- No rule that ♭ commutes with truncation is used, and no extensionality.
--
-- flat-split is inherited from the imports; nothing is split here.
module SetTruncationDiscrete where

open import Foundations
open import NativeFlatIdentity using (flat-set)
open import DiscretePullback using (counit-section-discrete)
open import OrdinaryTruncation

module _ {@♭ ℓ : Level} (@♭ τ : SetTruncation ℓ)
  {@♭ H : Set ℓ} (@♭ dH : Discrete H) where

  open SetTruncation τ

  private
    lift-point : H → ♭ (τ₀ H)
    lift-point h = flat-map ∣_∣₀ (inverse dH h)

    lift : τ₀ H → ♭ (τ₀ H)
    lift = τ₀-rec (flat-set τ₀-set) lift-point

    on-unit : (h : H) → counit (lift ∣ h ∣₀) ≡ ∣ h ∣₀
    on-unit h = ap counit (τ₀-rec-unit (flat-set τ₀-set) lift-point h)
              ∙ flat-map-counit ∣_∣₀ (inverse dH h)
              ∙ ap ∣_∣₀ (section dH h)

    lift-section : (z : τ₀ H) → counit (lift z) ≡ z
    lift-section = τ₀-unique τ₀-set (λ z → counit (lift z)) (λ z → z) on-unit

  truncation-discrete₀ : Discrete (τ₀ H)
  truncation-discrete₀ = counit-section-discrete lift lift-section
