{-# OPTIONS --safe --without-K --cohesion #-}

-- The ordinary truncation interfaces, in a module that is literally --safe.
-- Claude (Fable), 14 November 2026; fable-impl-22 (HANDOFF-37, items 1 and
-- 2; R37-NEXT-IMPLEMENTATION-SLICE-01, section 2).
--
-- WHY THIS MODULE EXISTS. The village already has these statements:
--   GlobalPropositions.FunExt₂, GlobalPropositions.Truncation
--   SharpPath.FunExtAt, ShapeChoice.FunExtAt
--   Foundations.PropositionalTruncation (level zero)
-- GlobalPropositions and ShapeChoice have --flat-split and import the shape
-- interface, so a --safe module cannot import them, although the
-- definitions themselves are ordinary. This module is the safe OWNER of the
-- same statements. The earlier files are not changed:
-- OrdinaryTruncationCompat has the adapters in both directions and the
-- checks that the statements and the carriers are the same.
--
-- EVERYTHING HERE IS A TYPE OF STRUCTURE. Nothing is postulated, and no
-- instance is constructed in this module. The operations of the two
-- records act on ORDINARY types, maps and elements; a caller that needs
-- the operations under a box supplies the record crisply.
--
-- LEVELS. A truncation structure of level ℓ has its carrier in Set ℓ and
-- its recursor into propositions (or sets) of the SAME level ℓ. The record
-- itself is in Set (lsuc ℓ). A recursor into another level b is NOT part of
-- the record and is not derivable from it. It is a separate certificate ON
-- THE SAME CARRIER, PropRecInto T b or SetRecInto T b, in
-- Set (lsuc (ℓ ⊔ b)). Nothing here replaces a carrier or resizes one.
module OrdinaryTruncation where

open import Foundations

------------------------------------------------------------------------
-- 1. Function extensionality from level a to level b.
--    FunExtBetween a b unfolds to the type that GlobalPropositions.FunExt₂
--    a b unfolds to, and FunExtBetween a a to the type of SharpPath.FunExtAt
--    a; a term of one is accepted where the other is asked.

FunExtBetween : (a b : Level) → Set (lsuc (a ⊔ b))
FunExtBetween a b = {X : Set a} {Y : X → Set b} {f g : (x : X) → Y x}
                  → ((x : X) → f x ≡ g x) → f ≡ g

------------------------------------------------------------------------
-- 2. Propositional truncation at one level. The four fields are those of
--    GlobalPropositions.Truncation, with the same names.

record PropTruncation (ℓ : Level) : Set (lsuc ℓ) where
  field
    ∥_∥ : Set ℓ → Set ℓ
    ∣_∣ : {A : Set ℓ} → A → ∥ A ∥
    squash : {A : Set ℓ} → IsProp ∥ A ∥
    ∥-rec : {A P : Set ℓ} → IsProp P → (A → P) → ∥ A ∥ → P

  -- There is no computation field. On a unit the recursor has the value of
  -- the handler up to a path, because the target is a proposition.
  ∥-rec-unit : {A P : Set ℓ} (P-prop : IsProp P) (f : A → P) (a : A)
             → ∥-rec P-prop f ∣ a ∣ ≡ f a
  ∥-rec-unit P-prop f a = P-prop (∥-rec P-prop f ∣ a ∣) (f a)

  ∥-map : {A B : Set ℓ} → (A → B) → ∥ A ∥ → ∥ B ∥
  ∥-map f = ∥-rec squash (λ a → ∣ f a ∣)

-- A recursor of the SAME carrier into the propositions of level b.
PropRecInto : {ℓ : Level} (T : PropTruncation ℓ) (b : Level)
            → Set (lsuc (ℓ ⊔ b))
PropRecInto {ℓ} T b = {A : Set ℓ} {P : Set b}
                    → IsProp P → (A → P) → PropTruncation.∥_∥ T A → P

-- The recursor of the record is the certificate at its own level.
own-level : {ℓ : Level} (T : PropTruncation ℓ) → PropRecInto T ℓ
own-level T = PropTruncation.∥-rec T

------------------------------------------------------------------------
-- 3. Set truncation at one level: the carrier is a set, and maps out of it
--    into a set of the same level are the maps out of the original type.
--    The recursor is NON-DEPENDENT. Its unit law and the uniqueness of maps
--    into a set are POINTWISE; no function extensionality is built in.

record SetTruncation (ℓ : Level) : Set (lsuc ℓ) where
  field
    τ₀ : Set ℓ → Set ℓ
    ∣_∣₀ : {A : Set ℓ} → A → τ₀ A
    τ₀-set : {A : Set ℓ} → IsSet (τ₀ A)
    τ₀-rec : {A D : Set ℓ} → IsSet D → (A → D) → τ₀ A → D
    τ₀-rec-unit : {A D : Set ℓ} (D-set : IsSet D) (f : A → D) (a : A)
                → τ₀-rec D-set f ∣ a ∣₀ ≡ f a
    τ₀-unique : {A D : Set ℓ} → IsSet D → (g h : τ₀ A → D)
              → ((a : A) → g ∣ a ∣₀ ≡ h ∣ a ∣₀)
              → (z : τ₀ A) → g z ≡ h z

  τ₀-map : {A B : Set ℓ} → (A → B) → τ₀ A → τ₀ B
  τ₀-map f = τ₀-rec τ₀-set (λ a → ∣ f a ∣₀)

  τ₀-map-unit : {A B : Set ℓ} (f : A → B) (a : A)
              → τ₀-map f ∣ a ∣₀ ≡ ∣ f a ∣₀
  τ₀-map-unit f = τ₀-rec-unit τ₀-set (λ a → ∣ f a ∣₀)

-- The same three operations of the SAME carrier against sets of level b.
record SetRecInto {ℓ : Level} (T : SetTruncation ℓ) (b : Level)
       : Set (lsuc (ℓ ⊔ b)) where
  open SetTruncation T
  field
    rec-into : {A : Set ℓ} {D : Set b} → IsSet D → (A → D) → τ₀ A → D
    rec-into-unit : {A : Set ℓ} {D : Set b} (D-set : IsSet D) (f : A → D)
                  → (a : A) → rec-into D-set f ∣ a ∣₀ ≡ f a
    unique-into : {A : Set ℓ} {D : Set b} → IsSet D → (g h : τ₀ A → D)
                → ((a : A) → g ∣ a ∣₀ ≡ h ∣ a ∣₀)
                → (z : τ₀ A) → g z ≡ h z

set-own-level : {ℓ : Level} (T : SetTruncation ℓ) → SetRecInto T ℓ
set-own-level T = record
  { rec-into = τ₀-rec
  ; rec-into-unit = τ₀-rec-unit
  ; unique-into = τ₀-unique
  }
  where open SetTruncation T
