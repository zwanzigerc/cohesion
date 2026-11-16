{-# OPTIONS --safe --without-K --cohesion #-}

-- An identification of two points of ♯ B from a point of ♯ (u ≡ v).
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, section 6;
-- CODISCRETE-POWER-NATIVE-ROUTE-01, section 2).
--
-- Literally --safe, and without --flat-split. Nothing is postulated. The one
-- hypothesis is function extensionality at one level, an ORDINARY argument
-- of the lemma.
--
-- PROVENANCE. A port of
--   Orbifolds/CrispTruncation.lagda, lines 63-66
--   (identifications-in-♯-from-sharp-ones)
--   sha256 e23e60be8196f44e83a5a11ec689692ca3be6b1ff46b18d57f79517371b00f05
-- read in the village folder sharp-power-reference-01/. The source is
-- written against TypeTopology and the module gist.CohesiveApartness.Sharp,
-- which was not among the files supplied; its names are matched by use:
--   _＝_, dfunext fe      builtin _≡_, the hypothesis below
--   rec-sharp             NativeSharp.sharp-rec
-- Only these four lines are ported. The module of the source has a second
-- parameter, a truncation structure; this lemma does not use it, and no
-- truncation occurs here. The other lemmas of the source are not ported.
--
-- THE HYPOTHESIS is written out, because GlobalPropositions, where FunExt₂
-- is defined, has --flat-split and cannot be imported by a module without
-- that flag. FunExtAt a unfolds to the type that FunExt₂ a a unfolds to; a
-- term of the latter is accepted where the former is asked (CodiscretePower
-- does that).
module SharpPath where

open import Foundations
open import NativeSharp using (♯; sharp-rec)

FunExtAt : (a : Level) → Set (lsuc a)
FunExtAt a = {X : Set a} {Y : X → Set a} {f g : (x : X) → Y x}
           → ((x : X) → f x ≡ g x) → f ≡ g

-- Why this is not an extraction of an ordinary sharp term. Extensionality
-- identifies the two CONSTANT functions (u ≡ v) → ♯ B at u and at v: a
-- point p of their domain is itself the path between their values. Then
-- sharp-rec is applied to that path of functions. On a constant function
-- sharp-rec gives a constant function, by the eta rule of the record ♯:
--   sharp-rec (λ _ → u) w  has the field  u .ε,  so it is u.
-- No field of an ordinary point of ♯ (u ≡ v) is used outside ♯.
sharp-path-extract : ∀ {a} → FunExtAt a
                   → {B : Set a} (u v : ♯ B) → ♯ (u ≡ v) → u ≡ v
sharp-path-extract fe u v =
  happly (ap sharp-rec (fe {f = λ _ → u} {g = λ _ → v} (λ p → p)))
