{-# OPTIONS --safe --without-K --cohesion #-}

-- Native Agda 2.9 sharp. This module uses neither shape postulates nor
-- --flat-split. The latter is unnecessary for the crisp identity lemma below.
module NativeSharp where

open import Foundations

record ♯ {a : Level} (@♯ A : Set a) : Set a where
  constructor sharp
  field
    @♯ ε : A
open ♯ public

sharp-unit : ∀ {a} {A : Set a} → A → ♯ A
sharp-unit x .ε = x

-- Elimination into an arbitrary type requires a crisp sharp term.
sharp-extract : {@♭ a : Level} {@♭ A : Set a} → (@♭ z : ♯ A) → A
sharp-extract z = z .ε

sharp-map : ∀ {a b} {A : Set a} {B : Set b}
          → (A → B) → ♯ A → ♯ B
sharp-map f z .ε = f (z .ε)

sharp-rec : ∀ {a b} {A : Set a} {B : Set b}
          → (A → ♯ B) → ♯ A → ♯ B
sharp-rec f z .ε = f (z .ε) .ε

sharp-map-unit : ∀ {a b} {A : Set a} {B : Set b}
               → (f : A → B) → (x : A)
               → sharp-map f (sharp-unit x) ≡ sharp-unit (f x)
sharp-map-unit f x = refl

sharp-rec-unit : ∀ {a b} {A : Set a} {B : Set b}
               → (f : A → ♯ B) → (x : A)
               → sharp-rec f (sharp-unit x) ≡ f x
sharp-rec-unit f x = refl

sharp-crisp-ind : {@♭ a : Level} {b : Level} {@♭ A : Set a}
                → (P : A → Set b) → ((@♭ x : A) → P x)
                → (x : A) → ♯ (P x)
sharp-crisp-ind P f x .ε = f x

-- The unit and counit of the flat/sharp adjunction.
flat-sharp-unit : {@♭ a : Level} {@♭ A : Set a} → A → ♯ (♭ A)
flat-sharp-unit x .ε = box x

flat-sharp-counit : {@♭ a : Level} {@♭ A : Set a} → ♭ (♯ A) → A
flat-sharp-counit (box z) = sharp-extract z

-- The adjunction transposes CRISP maps. Neither operation supplies a
-- counit ♯ A -> A on arbitrary ordinary sharp terms.
flat-to-sharp : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
              → (@♭ f : ♭ A → B) → A → ♯ B
flat-to-sharp f x .ε = f (box x)

sharp-to-flat : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
              → (@♭ g : A → ♯ B) → ♭ A → B
sharp-to-flat g (box x) = sharp-extract (g x)

flat-roundtrip : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
               → (@♭ f : ♭ A → B) → (x : ♭ A)
               → sharp-to-flat (flat-to-sharp f) x ≡ f x
flat-roundtrip f (box x) = refl

sharp-roundtrip : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
                → (@♭ g : A → ♯ B) → (x : A)
                → flat-to-sharp (sharp-to-flat g) x ≡ g x
sharp-roundtrip g x = refl

flat-triangle : {@♭ a : Level} {@♭ A : Set a} → (x : ♭ A)
              → flat-sharp-counit (flat-map flat-sharp-unit x) ≡ x
flat-triangle (box x) = refl

sharp-triangle : {@♭ a : Level} {@♭ A : Set a} → (z : ♯ A)
               → sharp-map flat-sharp-counit (flat-sharp-unit z) ≡ z
sharp-triangle z = refl

transport : ∀ {a b} {A : Set a} (P : A → Set b)
          → {x y : A} → x ≡ y → P x → P y
transport P refl px = px

-- Native sharp also derives this instance of crisp identity elimination.
-- It replaces a use of --flat-split without postulating an identity rule.
box-crisp-path : {@♭ a : Level} {@♭ A : Set a} {@♭ x y : A}
               → (@♭ p : x ≡ y) → box x ≡ box y
box-crisp-path {x = x} p = sharp-extract
  (transport (λ z → ♯ (box x ≡ box z)) p (sharp-unit refl))
