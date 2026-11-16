{-# OPTIONS --safe --without-K --cohesion #-}

-- Crisp elimination of a propositional truncation: to prove a proposition
-- from a CRISP mere element of a crisp type, a crisp element may be assumed.
-- Claude (Fable), 14 November 2026; fable-impl-22 (HANDOFF-37, item 1;
-- R37-NEXT-IMPLEMENTATION-SLICE-01, sections 3 and 4).
--
--   crisp-trunc-rec : IsProp P → ((@♭ a : A) → P) → (@♭ t : ∥ A ∥) → P
--
-- Literally --safe and without --flat-split. Nothing is postulated. The
-- truncation is a SUPPLIED structure (OrdinaryTruncation.PropTruncation),
-- and function extensionality at its level is a hypothesis.
--
-- PROVENANCE. A port of
--   Orbifolds/CrispTruncation.lagda, lines 68 to 96
--   sha256 e23e60be8196f44e83a5a11ec689692ca3be6b1ff46b18d57f79517371b00f05
-- read in the village folder sharp-power-reference-01/ (accepted source;
-- NATIVE-TRUNCATION-ACCEPTED-REUSE-02). Its first lemma, lines 63 to 66, is
-- SharpPath.sharp-path-extract of fable-impl-20 and is imported, not
-- repeated. The source is written against TypeTopology and the module
-- gist.CohesiveApartness.Sharp, which was not among the files supplied;
-- the names are matched by use:
--   _＝_, is-prop                    builtin _≡_, Foundations.IsProp
--   ∥_∥, ∣_∣, ∥∥-is-prop, ∥∥-rec     the fields of PropTruncation
--   unit-sharp, ε♯, crisp-elim-sharp  sharp-unit, ε, sharp-extract
--   _^♭                              box
-- The source takes its extensionality and its truncations at all universes
-- at once. Here both are at ONE level ℓ, which is all that the proofs use.
-- The eliminator of the source has a target in any universe; the form with
-- another target level is crisp-trunc-rec-into below, and it takes an
-- explicit recursor of the same carrier into that level.
--
-- WHAT IS CRISP AND WHAT IS NOT. Crisp: the level ℓ, the extensionality, the
-- truncation structure, the type A and the mere element t. The first three
-- because the whole term truncation-into-sharp t must be crisp for
-- sharp-extract; an ordinary structure would make it ordinary. Ordinary:
-- the proposition P, its proof, and the handler, which may all depend on
-- ordinary variables in scope. The witness binder of the handler is crisp.
--
-- WHAT THIS IS NOT. An ordinary mere element cannot be given to the
-- eliminator (CrispTruncationOrdinaryWitness.agda.fail). No element of A is
-- chosen. truncation-into-sharp is a map ∥ A ∥ → ♯ ∥ ♭ A ∥ on ORDINARY
-- mere elements; it is weaker than a map ∥ A ∥ → ∥ ♭ A ∥, which is not
-- claimed.
module CrispTruncation where

open import Foundations
open import NativeSharp using (♯; ε; sharp-unit; sharp-extract)
open import SharpPath using (FunExtAt; sharp-path-extract)
open import OrdinaryTruncation

-- ♯ of a proposition is a proposition. All arguments are ordinary.
-- (Source, lines 68 to 74.) Inside the field both projections are
-- available; the path lies in ♯ P by the eta rule of the record ♯.
sharp-prop : ∀ {a} → FunExtAt a → {P : Set a} → IsProp P → IsProp (♯ P)
sharp-prop fe {P} P-prop u v = sharp-path-extract fe u v w
  where
  w : ♯ (u ≡ v)
  w .ε = ap sharp-unit (P-prop (u .ε) (v .ε))

module _ {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ T : PropTruncation ℓ) where

  open PropTruncation T

  -- (Source, lines 76 to 81.) The handler g is defined under ♯, where its
  -- ordinary argument may be boxed. The recursor of T is used at its own
  -- level: the target ♯ ∥ ♭ A ∥ is in Set ℓ.
  truncation-into-sharp : {@♭ A : Set ℓ} → ∥ A ∥ → ♯ ∥ ♭ A ∥
  truncation-into-sharp {A} = ∥-rec (sharp-prop fe squash) g
    where
    g : A → ♯ ∥ ♭ A ∥
    g a .ε = ∣ box a ∣

  -- (Source, lines 83 to 86.) Legal only because the argument is crisp.
  crisp-trunc-flat : {@♭ A : Set ℓ} → (@♭ t : ∥ A ∥) → ∥ ♭ A ∥
  crisp-trunc-flat t = sharp-extract (truncation-into-sharp t)

  -- (Source, lines 88 to 96, at the level of T.)
  crisp-trunc-rec : {@♭ A : Set ℓ} {P : Set ℓ}
                  → IsProp P → ((@♭ a : A) → P) → (@♭ t : ∥ A ∥) → P
  crisp-trunc-rec {A} {P} P-prop h t = ∥-rec P-prop γ (crisp-trunc-flat t)
    where
    γ : ♭ A → P
    γ (box a) = h a

  -- The same into a proposition of another level b, given a recursor of
  -- THE SAME carrier into that level. The certificate, the level b, the
  -- proposition and the handler are ordinary. The step through ♯ still
  -- uses the recursor of T at its own level; no extensionality at b.
  crisp-trunc-rec-into : {b : Level} (into : PropRecInto T b)
                       → {@♭ A : Set ℓ} {P : Set b}
                       → IsProp P → ((@♭ a : A) → P) → (@♭ t : ∥ A ∥) → P
  crisp-trunc-rec-into into {A} {P} P-prop h t =
    into P-prop γ (crisp-trunc-flat t)
    where
    γ : ♭ A → P
    γ (box a) = h a

  -- No computation rule is claimed. On the unit at a crisp point the value
  -- is that of the handler up to a path, because P is a proposition.
  crisp-trunc-rec-unit : {@♭ A : Set ℓ} {P : Set ℓ} (P-prop : IsProp P)
                       → (h : (@♭ a : A) → P) (@♭ a : A)
                       → crisp-trunc-rec P-prop h ∣ a ∣ ≡ h a
  crisp-trunc-rec-unit P-prop h a =
    P-prop (crisp-trunc-rec P-prop h ∣ a ∣) (h a)
