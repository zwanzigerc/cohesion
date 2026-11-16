{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The safe interfaces of OrdinaryTruncation against the interfaces that
-- the village already has: the statements are the same types, the records
-- are converted in both directions with every operation kept, and the
-- carrier in particular. Claude (Fable), 14 November 2026; fable-impl-22
-- (HANDOFF-37, item 1; R37-NEXT-IMPLEMENTATION-SLICE-01, sections 2 and 5).
--
-- Nothing is postulated, and no equality of records is ASSUMED: the two
-- round trips below are proved, by refl, from the eta rule of records.
-- No earlier module is changed. This module has --flat-split because it
-- imports GlobalPropositions and ShapeChoice; it matches on no crisp
-- argument.
module OrdinaryTruncationCompat where

open import Foundations
open import GlobalPrecohesion using (Merely)
open import GlobalPropositions
  using (FunExt₂; Truncation; to-truncation; from-truncation)
open import TruncationDiscrete using (truncation-discrete)
open import OrdinaryTruncation
import SharpPath
import ShapeChoice
import CrispTruncation

------------------------------------------------------------------------
-- 1. Function extensionality: one type under four names.

between-is-FunExt₂ : (a b : Level) → FunExtBetween a b ≡ FunExt₂ a b
between-is-FunExt₂ a b = refl

between-is-sharp-path : (a : Level)
                      → FunExtBetween a a ≡ SharpPath.FunExtAt a
between-is-sharp-path a = refl

between-is-shape-choice : (a : Level)
                        → FunExtBetween a a ≡ ShapeChoice.FunExtAt a
between-is-shape-choice a = refl

between-is-foundations : FunExtBetween lzero lzero ≡ FunExt
between-is-foundations = refl

------------------------------------------------------------------------
-- 2. PropTruncation ℓ and GlobalPropositions.Truncation ℓ.

to-global : {ℓ : Level} → PropTruncation ℓ → Truncation ℓ
to-global T = record
  { ∥_∥ = ∥_∥ ; ∣_∣ = ∣_∣ ; squash = squash ; ∥-rec = ∥-rec }
  where open PropTruncation T

from-global : {ℓ : Level} → Truncation ℓ → PropTruncation ℓ
from-global t = record
  { ∥_∥ = ∥_∥ ; ∣_∣ = ∣_∣ ; squash = squash ; ∥-rec = ∥-rec }
  where open Truncation t

to-from-global : {ℓ : Level} (t : Truncation ℓ)
               → to-global (from-global t) ≡ t
to-from-global t = refl

from-to-global : {ℓ : Level} (T : PropTruncation ℓ)
               → from-global (to-global T) ≡ T
from-to-global T = refl

-- The carrier is the same type, in both directions.
same-carrier-to : {ℓ : Level} (T : PropTruncation ℓ) (A : Set ℓ)
                → Truncation.∥_∥ (to-global T) A ≡ PropTruncation.∥_∥ T A
same-carrier-to T A = refl

same-carrier-from : {ℓ : Level} (t : Truncation ℓ) (A : Set ℓ)
                  → PropTruncation.∥_∥ (from-global t) A
                    ≡ Truncation.∥_∥ t A
same-carrier-from t A = refl

------------------------------------------------------------------------
-- 3. Level zero: Foundations.PropositionalTruncation.

to-foundations : PropTruncation lzero → PropositionalTruncation
to-foundations T = record
  { ∥_∥ = ∥_∥ ; ∣_∣ = ∣_∣ ; trunc-is-prop = squash ; trunc-rec = ∥-rec }
  where open PropTruncation T

from-foundations : PropositionalTruncation → PropTruncation lzero
from-foundations t = record
  { ∥_∥ = ∥_∥ ; ∣_∣ = ∣_∣ ; squash = trunc-is-prop ; ∥-rec = trunc-rec }
  where open PropositionalTruncation t

to-from-foundations : (t : PropositionalTruncation)
                    → to-foundations (from-foundations t) ≡ t
to-from-foundations t = refl

from-to-foundations : (T : PropTruncation lzero)
                    → from-foundations (to-foundations T) ≡ T
from-to-foundations T = refl

------------------------------------------------------------------------
-- 4. Merely, the Church form of GlobalPrecohesion: the existing maps of
--    GlobalPropositions, against the carrier of T itself.

module _ {@♭ ℓ : Level} (T : PropTruncation ℓ) where

  open PropTruncation T

  merely-to-truncation : {A : Set ℓ} → Merely A → ∥ A ∥
  merely-to-truncation = to-truncation (to-global T)

  truncation-to-merely : {A : Set ℓ} → ∥ A ∥ → Merely A
  truncation-to-merely = from-truncation (to-global T)

------------------------------------------------------------------------
-- 5. The two lemmas about a truncation that take a crisp structure, for
--    both records. truncation-discrete is the lemma of fable-impl-20,
--    unchanged; crisp-trunc-rec is CrispTruncation's.

prop-truncation-discrete : {@♭ ℓ : Level} (@♭ T : PropTruncation ℓ)
                         → {@♭ A : Set ℓ} (@♭ dA : Discrete A)
                         → Discrete (PropTruncation.∥_∥ T A)
prop-truncation-discrete T dA = truncation-discrete (to-global T) dA

crisp-trunc-rec-global : {@♭ ℓ : Level} (@♭ fe : FunExt₂ ℓ ℓ)
                       → (@♭ t : Truncation ℓ)
                       → {@♭ A : Set ℓ} {P : Set ℓ} → IsProp P
                       → ((@♭ a : A) → P)
                       → (@♭ x : Truncation.∥_∥ t A) → P
crisp-trunc-rec-global fe t =
  CrispTruncation.crisp-trunc-rec fe (from-global t)
