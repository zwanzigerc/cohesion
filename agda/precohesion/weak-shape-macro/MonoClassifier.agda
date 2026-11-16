{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The base classifier classifies whole crisp monos between discrete types
-- of level i. Claude (Fable), 14 November 2026; fable-impl-19 (HANDOFF-35,
-- item 3; BASE-CLASSIFIER-NATIVE-AUDIT-01, sections 3 and 8.4).
--
-- Nothing is postulated. No shape, no stability, no truncation, no
-- resizing; continuity and the Nullstellensatz do not occur.
--
-- THE INPUT is one whole crisp mono: crisp types D, B : Set i, crisp proofs
-- that they are discrete, a crisp map m : D → B, and a crisp proof that
-- every fibre of m is a proposition. An ordinary family of propositions
-- over B is not an input of this module, and no statement here is about
-- one. (Sethood of B and D is not used. If B is a set and m is injective,
-- SmallPropositions.injective-fibres gives the last hypothesis.)
--
-- Characteristic (no extensionality at all):
--   χ : B → O i          at a crisp b, the code of Fiber m b with the
--                        discreteness that ShapeElim.FiberDiscrete proves;
--                        extended to all b by induction on the discrete
--                        type B (GlobalPrecohesion.discrete-elim)
--   χ-β                  its computation rule at a crisp b
--                        (discrete-elim-β)
--   fibre-equiv          El (χ b) ≃ Fiber m b for every ORDINARY b
--
-- Classification (crisp fe : FunExt₂ i i, crisp pe : PropExt i, the two
-- hypotheses of BaseClassifierLaws):
--   truth-square         χ (m x) ≡ top
--   gap-is-equiv         D ≃ Σ (b : B). χ b ≡ top: the square is a pullback.
--                        D is of Set i and the Σ of Set (lsuc i); the
--                        equivalence is between the two types as they are.
--   unique               a CRISP map χ′ with CRISP fibrewise comparison
--                        maps agrees with χ at every point
--   unique-from-square   the same from a crisp pullback square for χ′
--   unique-map           χ′ ≡ χ as maps. This needs one more hypothesis,
--                        FunExt₂ i (lsuc i): the maps go from a type of
--                        Set i to a type of Set (lsuc i). It is an
--                        argument of this one statement and of
--                        Reindexing.reindex-map, of nothing else.
--
-- Reindexing (the same two hypotheses): for a whole crisp f : B′ → B from
-- a discrete type, the pulled-back mono is again an input, and its
-- characteristic map is χ ∘ f, pointwise.
--
-- Uniqueness is for crisp competitors. For an ordinary map χ′ : B → O i
-- with ordinary comparison maps nothing is proved here: an ordinary
-- implication cannot be boxed.
module MonoClassifier where

open import Foundations
open import NativeSharp using (transport)
open import Adjointify using (quasi-inverse)
open import PullbackSetFibers
  using (Pullback; fiber-fst-out; fiber-fst-in; fiber-fst-retraction)
open import DiscretePullback using (pullback-discrete)
open import GlobalPrecohesion using (discrete-elim; discrete-elim-β)
open import GlobalPropositions using (FunExt₂)
open import ShapeElim using (module FiberDiscrete)
open import SmallPropositions
open import BaseClassifier
open import BaseClassifierLaws using (module Laws)

------------------------------------------------------------------------
-- 1. The characteristic map and the fibre comparison. No hypothesis.

module Characteristic
  {@♭ i : Level} {@♭ B D : Set i}
  (@♭ dB : Discrete B) (@♭ dD : Discrete D)
  (@♭ m : D → B) (@♭ mono : (b : B) → IsProp (Fiber m b)) where

  -- A fibre over a crisp point of a crisp map between discrete types.
  fibre-discrete : (@♭ b : B) → Discrete (Fiber m b)
  fibre-discrete b = FiberDiscrete.discrete dB dD m b

  χ-at : (@♭ b : B) → O i
  χ-at b = code (Fiber m b) (mono b) (fibre-discrete b)

  χ : B → O i
  χ = discrete-elim dB (λ _ → O i) χ-at

  χ-β : (@♭ b : B) → χ b ≡ χ-at b
  χ-β = discrete-elim-β dB (λ _ → O i) χ-at

  -- El (χ-at b) is Fiber m b by computation. So at a crisp b the two maps
  -- are transports along χ-β; induction on B extends them to every b.
  Comparison : B → Set i
  Comparison b = (El (χ b) → Fiber m b) × (Fiber m b → El (χ b))

  private
    comparison-at : (@♭ b : B) → Comparison b
    comparison-at b = transport El (χ-β b) , transport El (sym (χ-β b))

  comparison : (b : B) → Comparison b
  comparison = discrete-elim dB Comparison comparison-at

  to-fibre : (b : B) → El (χ b) → Fiber m b
  to-fibre b = fst (comparison b)

  from-fibre : (b : B) → Fiber m b → El (χ b)
  from-fibre b = snd (comparison b)

  -- Both sides are propositions. The inverse is from-fibre b by computation.
  fibre-equiv : (b : B) → IsEquiv (to-fibre b)
  fibre-equiv b =
    prop-equiv (El-is-prop (χ b)) (mono b) (to-fibre b) (from-fibre b)

------------------------------------------------------------------------
-- 2. The truth square, and uniqueness.

module Classification
  {@♭ i : Level} (@♭ fe : FunExt₂ i i) (@♭ pe : PropExt i)
  {@♭ B D : Set i}
  (@♭ dB : Discrete B) (@♭ dD : Discrete D)
  (@♭ m : D → B) (@♭ mono : (b : B) → IsProp (Fiber m b)) where

  open Characteristic dB dD m mono public
  open Laws fe pe

  -- The square  D → 1, m, χ, top  commutes.
  truth-square : (x : D) → χ (m x) ≡ top
  truth-square x = truth-in (χ (m x)) (from-fibre (m x) (x , refl))

  -- It is a pullback: D is the fibre of χ over top.
  TruthPullback : Set (lsuc i)
  TruthPullback = Σ B (λ b → χ b ≡ top)

  gap : D → TruthPullback
  gap x = m x , truth-square x

  gap-inverse : TruthPullback → D
  gap-inverse (b , e) = fst (to-fibre b (truth-out (χ b) e))

  gap-is-equiv : IsEquiv gap
  gap-is-equiv = quasi-inverse gap-inverse gap-section gap-retraction
    where
    gap-section : (t : TruthPullback) → gap (gap-inverse t) ≡ t
    gap-section (b , e) =
      subtype-path (λ c → O-is-set (χ c) top)
        (snd (to-fibre b (truth-out (χ b) e)))

    gap-retraction : (x : D) → gap-inverse (gap x) ≡ x
    gap-retraction x =
      ap fst (mono (m x)
        (to-fibre (m x) (truth-out (χ (m x)) (truth-square x))) (x , refl))

  -- Uniqueness, pointwise. The competing map and its two comparison maps
  -- are crisp: at a crisp b they are the crisp implications that code
  -- extensionality asks for. Induction on B gives every b.
  unique : (@♭ χ′ : B → O i)
         → (@♭ to′ : (b : B) → El (χ′ b) → Fiber m b)
         → (@♭ from′ : (b : B) → Fiber m b → El (χ′ b))
         → (b : B) → χ′ b ≡ χ b
  unique χ′ to′ from′ = discrete-elim dB (λ b → χ′ b ≡ χ b) at-crisp
    where
    at-crisp : (@♭ b : B) → χ′ b ≡ χ b
    at-crisp b = code-ext (χ′ b) (χ-at b) (to′ b) (from′ b) ∙ sym (χ-β b)

  -- The same for a competitor given with a crisp pullback square: a crisp
  -- proof that the square commutes, and a crisp map from its fibre of
  -- truth to the fibres of m.
  unique-from-square :
    (@♭ χ′ : B → O i)
    → (@♭ square : (x : D) → χ′ (m x) ≡ top)
    → (@♭ cartesian : (b : B) → χ′ b ≡ top → Fiber m b)
    → (b : B) → χ′ b ≡ χ b
  unique-from-square χ′ square cartesian =
    unique χ′
      (λ b p → cartesian b (truth-in (χ′ b) p))
      (λ b z → truth-out (χ′ b)
                 (transport (λ c → χ′ c ≡ top) (snd z) (square (fst z))))

  -- Equality of the two MAPS. The additional hypothesis is function
  -- extensionality from Set i into Set (lsuc i); it is not needed crisply.
  unique-map : FunExt₂ i (lsuc i)
             → (@♭ χ′ : B → O i)
             → (@♭ to′ : (b : B) → El (χ′ b) → Fiber m b)
             → (@♭ from′ : (b : B) → Fiber m b → El (χ′ b))
             → χ′ ≡ χ
  unique-map fe₊ χ′ to′ from′ = fe₊ (unique χ′ to′ from′)

------------------------------------------------------------------------
-- 3. Reindexing along a whole crisp map of discrete types.

module Reindexing
  {@♭ i : Level} (@♭ fe : FunExt₂ i i) (@♭ pe : PropExt i)
  {@♭ B B′ D : Set i}
  (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′) (@♭ dD : Discrete D)
  (@♭ m : D → B) (@♭ mono : (b : B) → IsProp (Fiber m b))
  (@♭ f : B′ → B) where

  -- The pulled-back mono is again a whole crisp mono of discrete types
  -- of level i: finite limits of discrete types (DiscretePullback).
  D′ : Set i
  D′ = Pullback m f

  m′ : D′ → B′
  m′ = fst

  dD′ : Discrete D′
  dD′ = pullback-discrete dB dB′ dD m f

  mono′ : (b′ : B′) → IsProp (Fiber m′ b′)
  mono′ b′ =
    retract-is-prop fiber-fst-out fiber-fst-in fiber-fst-retraction
      (mono (f b′))

  module Base = Classification fe pe dB dD m mono
  module Pulled = Classification fe pe dB′ dD′ m′ mono′

  -- The characteristic map of the pulled-back mono is χ ∘ f: the latter
  -- is a crisp competitor, and the fibres of m′ over b′ are those of m
  -- over f b′.
  reindex : (b′ : B′) → Base.χ (f b′) ≡ Pulled.χ b′
  reindex =
    Pulled.unique (λ b′ → Base.χ (f b′))
      (λ b′ p → fiber-fst-in (Base.to-fibre (f b′) p))
      (λ b′ z → Base.from-fibre (f b′) (fiber-fst-out z))

  reindex-map : FunExt₂ i (lsuc i) → (λ b′ → Base.χ (f b′)) ≡ Pulled.χ
  reindex-map fe₊ = fe₊ reindex
