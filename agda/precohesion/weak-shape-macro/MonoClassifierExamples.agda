{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Classification of whole crisp monos in use. Claude (Fable), 14 November
-- 2026; fable-impl-19 (HANDOFF-35, the bounded client of item 3).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters:
--   section 1   an arbitrary whole crisp mono of level i; crisp fe and pe;
--               for the two equalities of MAPS also FunExt₂ i (lsuc i),
--               an ordinary parameter
--   section 2   crisp fe and pe at level zero
--   section 3   the same
-- Sections 2 and 3 compute the classifier of one concrete mono, the point
-- true : 1 → Bool, and of its pullback along negation.
module MonoClassifierExamples where

open import Foundations
open import Agda.Builtin.Bool
open import CaptureContext using (CrispUnitAt; end-at; unit-at-discrete)
open import DecidableData using (⊥)
open import BoolDecidable using (bool-is-set; bool-is-discrete)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import BaseClassifier
open import BaseClassifierLaws using (module Laws)
open import MonoClassifier
open import BaseClassifierExamples using (bottom)

------------------------------------------------------------------------
-- 1. An arbitrary whole crisp mono.

module Generic {@♭ i : Level}
  (@♭ fe : FunExt₂ i i) (@♭ pe : PropExt i)
  {@♭ B D : Set i}
  (@♭ dB : Discrete B) (@♭ dD : Discrete D)
  (@♭ m : D → B) (@♭ mono : (b : B) → IsProp (Fiber m b)) where

  -- The characteristic map and the fibre comparison need no hypothesis:
  -- they are taken from the module that has none.
  module Before = Characteristic dB dD m mono

  characteristic : B → O i
  characteristic = Before.χ

  fibres : (b : B) → IsEquiv (Before.to-fibre b)
  fibres = Before.fibre-equiv

  open Classification fe pe dB dD m mono

  -- The classification is about that same map.
  same-map : χ ≡ characteristic
  same-map = refl

  -- The square commutes and is a pullback. D : Set i, the pullback is of
  -- Set (lsuc i).
  commutes : (x : D) → χ (m x) ≡ top
  commutes = truth-square

  domain-is-pullback : IsEquiv gap
  domain-is-pullback = gap-is-equiv

  pullback-level : Set (lsuc i)
  pullback-level = TruthPullback

  -- Uniqueness applied to χ itself with its own comparison maps: χ, as a
  -- closed term of crisp data, is a crisp competitor.
  self : (b : B) → χ b ≡ χ b
  self = unique χ to-fibre from-fibre

  -- Equality of maps, under the larger-target extensionality only. (The
  -- statement χ ≡ χ is also refl; what is shown is the type of the
  -- hypothesis that unique-map takes.)
  module _ (fe₊ : FunExt₂ i (lsuc i)) where

    self-map : χ ≡ χ
    self-map = unique-map fe₊ χ to-fibre from-fibre

  -- Reindexing along a whole crisp map from a discrete type.
  module _ {@♭ B′ : Set i} (@♭ dB′ : Discrete B′) (@♭ f : B′ → B) where

    open Reindexing fe pe dB dB′ dD m mono f

    pulled-back : (b′ : B′) → χ (f b′) ≡ Pulled.χ b′
    pulled-back = reindex

    pulled-back-map : FunExt₂ i (lsuc i) → (λ b′ → χ (f b′)) ≡ Pulled.χ
    pulled-back-map = reindex-map

------------------------------------------------------------------------
-- 2. The point true : 1 → Bool, at level zero.

module TruePoint
  (@♭ fe : FunExt₂ lzero lzero) (@♭ pe : PropExt lzero) where

  One : Set
  One = CrispUnitAt lzero

  point : One → Bool
  point _ = true

  -- Bool is a set and the map is injective.
  point-mono : (b : Bool) → IsProp (Fiber point b)
  point-mono =
    injective-fibres point bool-is-set (λ x y _ → unit-at-is-prop x y)

  open Laws fe pe
  open Classification fe pe bool-is-discrete unit-at-discrete point point-mono

  -- Over true the classifier is truth.
  at-true : χ true ≡ top
  at-true = truth-square end-at

  -- Over false it is not: the fibre is empty.
  private
    true-is-not-false : true ≡ false → ⊥
    true-is-not-false ()

  not-at-false : χ false ≡ top → ⊥
  not-at-false e =
    true-is-not-false (snd (to-fibre false (truth-out (χ false) e)))

  -- The classifier, computed: a competitor defined by cases, with its
  -- comparison maps, agrees with χ.
  by-cases : Bool → O lzero
  by-cases true = top
  by-cases false = bottom

  to′ : (b : Bool) → El (by-cases b) → Fiber point b
  to′ true _ = end-at , refl
  to′ false ()

  from′ : (b : Bool) → Fiber point b → El (by-cases b)
  from′ true _ = end-at
  from′ false (_ , ())

  computed : (b : Bool) → by-cases b ≡ χ b
  computed = unique by-cases to′ from′

  at-false : χ false ≡ bottom
  at-false = sym (computed false)

  -- The same competitor through its pullback square.
  computed-from-square : (b : Bool) → by-cases b ≡ χ b
  computed-from-square =
    unique-from-square by-cases (λ _ → refl) cartesian
    where
    cartesian : (b : Bool) → by-cases b ≡ top → Fiber point b
    cartesian true _ = end-at , refl
    cartesian false e = to′ false (truth-out bottom e)

------------------------------------------------------------------------
-- 3. Its pullback along negation classifies the point false.

module Negated
  (@♭ fe : FunExt₂ lzero lzero) (@♭ pe : PropExt lzero) where

  open TruePoint fe pe using (point; point-mono)

  not : Bool → Bool
  not true = false
  not false = true

  open Reindexing fe pe bool-is-discrete bool-is-discrete unit-at-discrete
    point point-mono not

  -- The classifier of the pulled-back mono is χ ∘ not.
  law : (b : Bool) → Base.χ (not b) ≡ Pulled.χ b
  law = reindex

  -- So it is truth over false.
  at-false : Pulled.χ false ≡ top
  at-false = sym (reindex false) ∙ Base.truth-square end-at
