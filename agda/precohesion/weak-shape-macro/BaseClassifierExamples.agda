{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The base classifier in use: its carrier before any hypothesis, and its
-- laws under the two hypotheses. Claude (Fable), 14 November 2026;
-- fable-impl-19 (HANDOFF-35, the bounded client of items 1 and 2).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters:
--   section 1   none (a crisp level)
--   section 2   crisp fe : FunExt₂ i i and crisp pe : PropExt i
-- The checks written `refl` are computations of the compiler.
module BaseClassifierExamples where

open import Foundations
open import CaptureContext using (CrispUnitAt; end-at)
open import DecidableData using (⊥)
open import NativeFlatIdentity using (box-identity-equiv; box-path-to-flat)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import BaseClassifier
open import BaseClassifierLaws using (module Laws)

------------------------------------------------------------------------
-- 1. Before any hypothesis, at an arbitrary crisp level.

module Carrier {@♭ i : Level} where

  -- The levels of the three exports.
  carrier : Set (lsuc i)
  carrier = O i

  decoding : O i → Set i
  decoding = El

  truth : O i
  truth = top

  -- The carrier is, by definition, ♭ of the codes with their proofs of
  -- discreteness. It is not ♭ (HProp i).
  carrier-unfolds : O i ≡ ♭ (Σ (♭ (Σ (Set i) IsProp)) d)
  carrier-unfolds = refl

  -- Truth decodes to the one-point type of level i, and holds.
  truth-decodes : El (top {i}) ≡ CrispUnitAt i
  truth-decodes = refl

  truth-holds : El (top {i})
  truth-holds = top-holds

  -- O i is discrete: every point has a crisp representative.
  lift : O i → ♭ (O i)
  lift = inverse O-discrete

  lift-section : (r : O i) → counit (lift r) ≡ r
  lift-section = section O-discrete

  -- A crisp discrete proposition is a code, and decodes to itself with
  -- the proofs that were stored.
  module _ (@♭ P : Set i) (@♭ h : IsProp P) (@♭ dP : Discrete P) where

    decodes : El (code P h dP) ≡ P
    decodes = refl

    stored-prop : El-is-prop (code P h dP) ≡ h
    stored-prop = refl

    stored-discrete : El-discrete (code P h dP) ≡ dP
    stored-discrete = refl

  -- The decoded type of a CRISP code is discrete; so a point of it has a
  -- crisp representative.
  crisp-point : (@♭ r : O i) → El r → ♭ (El r)
  crisp-point r = inverse (El-discrete r)

  -- For an ORDINARY code one eliminates it first.
  some-prop : (r : O i) → IsProp (El r)
  some-prop = O-elim (λ r → IsProp (El r)) (λ P h dP → h)

  -- The comparison to the ambient propositions.
  to-ambient : O i → HProp i
  to-ambient = decode

  to-ambient-top : fst (to-ambient (top {i})) ≡ CrispUnitAt i
  to-ambient-top = refl

-- The carrier at two particular levels: O lzero is a type of Set₁, and
-- O (lsuc lzero) is a type of Set₂.
carrier₀ : Set₁
carrier₀ = O lzero

carrier₁ : Set₂
carrier₁ = O (lsuc lzero)

-- Two codes of level zero: truth, and the empty proposition.
⊥-discrete : Discrete ⊥
⊥-discrete ()

bottom : O lzero
bottom = code ⊥ (λ ()) ⊥-discrete

bottom-fails : El bottom → ⊥
bottom-fails x = x

------------------------------------------------------------------------
-- 2. The laws. The hypotheses are parameters; they are not proved here
--    and are not postulated in any module of the project.

module WithLaws {@♭ i : Level}
  (@♭ fe : FunExt₂ i i) (@♭ pe : PropExt i) where

  open Laws fe pe

  -- The laws are about the carrier and the truth point of section 1: the
  -- types below name BaseClassifier.O and BaseClassifier.top, which were
  -- defined before fe and pe.
  carrier-is-set : IsSet (Carrier.carrier {i})
  carrier-is-set = O-is-set

  truth-is-unchanged : Carrier.truth {i} ≡ top
  truth-is-unchanged = refl

  -- A discrete set: both halves, for the same type.
  discrete-set : IsSet (O i) × Discrete (O i)
  discrete-set = O-is-set , O-discrete

  -- The stored proofs do not matter: a crisp proposition has one code.
  one-code : (@♭ P : Set i) (@♭ h h′ : IsProp P) (@♭ dP dP′ : Discrete P)
           → code P h dP ≡ code P h′ dP′
  one-code P h h′ dP dP′ =
    code-ext (code P h dP) (code P h′ dP′) (λ x → x) (λ x → x)

  -- Crisp codes with crisp implications both ways are equal.
  crisp-ext : (@♭ r s : O i) (@♭ f : El r → El s) (@♭ g : El s → El r)
            → r ≡ s
  crisp-ext = code-ext

  -- The fibre of truth, for an ORDINARY code and an ordinary inhabitant.
  holds-gives-top : (r : O i) → El r → r ≡ top
  holds-gives-top = truth-in

  top-gives-holds : (r : O i) → r ≡ top → El r
  top-gives-holds = truth-out

  fibre-of-truth : (r : O i) → IsEquiv (truth-out r)
  fibre-of-truth = truth-fibre

  -- Its inverse is truth-in, by computation.
  fibre-inverse : (r : O i) (p : El r)
                → inverse (truth-fibre r) p ≡ truth-in r p
  fibre-inverse r p = refl

  -- top : 1 → O i is a mono: its fibres are propositions.
  truth-is-mono : (r : O i) → IsProp (r ≡ top)
  truth-is-mono r = O-is-set r top

  -- The identity types of ♭ at work: a path between two crisp codes is a
  -- crisp path of their underlying pairs.
  path-of-codes : (@♭ c c′ : C i) → box c ≡ box c′ → ♭ (c ≡ c′)
  path-of-codes = box-path-to-flat

  path-of-codes-equiv : (@♭ c c′ : C i) → IsEquiv (path-of-codes c c′)
  path-of-codes-equiv = box-identity-equiv

-- At level zero truth and the empty proposition are different codes. No
-- hypothesis: transport along the path.
top-is-not-bottom : top ≡ bottom → ⊥
top-is-not-bottom e = at e end-at
  where
  at : {r s : O lzero} → r ≡ s → El r → El s
  at refl x = x
