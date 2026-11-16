{-# OPTIONS --safe --without-K --cohesion #-}

-- The native-sharp adapter of the connected-interval theorem.
-- Opus, 13 November 2026; opus-connected-interval-01, implementing
-- CONNECTED-INTERVAL-PLAN-FABLE-01.txt section 3 (identical in content to
-- the checked ConnectedIntervalNativeProbe, without its selector part,
-- which lives in precohesion-shape0/ConnectedSelector.agda).
--
-- Literally --safe: imports Foundations and NativeSharp only. It must not
-- import CaptureContext (--flat-split), which is why the two-point type is
-- its own data type at every level and not Raise ℓ Bool.
--
-- Nothing about ♯ and coproducts is used: Two is matched inside the sharp
-- field of the result, never ♯ (Two ℓ) outside it. There is no map ♯ A → A
-- on ordinary terms here. Both endpoint equations are refl, by computation
-- of `choose` and the eta rules of the record ♯ and of Σ.
module ConnectedIntervalNative where

open import Foundations
open import NativeSharp using (♯; ε; sharp-unit)

-- A two-point type at every level.
data Two (ℓ : Level) : Set ℓ where
  left right : Two ℓ

-- The endpoints depend on the level only (plan 3 (b)).
i₀ i₁ : {ℓ : Level} → ♯ (Two ℓ)
i₀ = sharp-unit left
i₁ = sharp-unit right

module _ {ℓ : Level} {A : Set ℓ} where

  choose : Two ℓ → A → A → A
  choose left a b = a
  choose right a b = b

  -- The selector on sharp types.
  m : (♯ A × ♯ A) × ♯ (Two ℓ) → ♯ A
  m w .ε = choose (snd w .ε) (fst (fst w) .ε) (snd (fst w) .ε)

  m-left : (x : ♯ A × ♯ A) → m (x , i₀) ≡ fst x
  m-left x = refl

  m-right : (x : ♯ A × ♯ A) → m (x , i₁) ≡ snd x
  m-right x = refl
