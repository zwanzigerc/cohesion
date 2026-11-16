{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The bounded quantifier in use. Claude (Fable), 14 November 2026;
-- fable-impl-20 (HANDOFF-36, the bounded client of section 1).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters:
--   section 1   an arbitrary crisp discrete F : Set (lsuc i) with ONE
--               shape datum of F → O i; crisp fe-i, pe-i, fe-j, pe-j; and
--               fe-ji, an ordinary parameter
--   section 2   the same at the one-point type
--   section 3   the same at the two-point type One ⊎ One
-- Sections 2 and 3 read the quantifier off at two concrete index types:
-- over one point it is the code itself, over two points it is the binary
-- meet. In both the shape datum of the power is still a parameter: no
-- shape is made here.
module BoundedQuantifierExamples where

open import Foundations
open import CaptureContext using (CrispUnitAt; end-at; unit-at-discrete)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import BaseClassifier hiding (C)
open import TruncationDiscrete using (_⊎_; inl; inr; sum-discrete)
open import BoundedQuantifier

------------------------------------------------------------------------
-- 1. An arbitrary fixed power.

module Generic {@♭ i : Level} {@♭ F : Set (lsuc i)}
  (@♭ dF : Discrete F)
  (@♭ sQ : ShapeData (F → O i))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (fe-ji : FunExt₂ (lsuc i) i) where

  -- The carriers are formed without any of the hypotheses.
  module Before = Carrier F

  open Quantifier dF sQ fe-i pe-i fe-j
  open Decoding fe-ji
  open Truth pe-j

  -- The quantifier is about those same carriers.
  same-power : Q ≡ Before.Q
  same-power = refl

  same-truth : v ≡ Before.v
  same-truth = refl

  -- Its type: from the power, of Set (lsuc i), into the classifier of the
  -- next level, of Set (lsuc (lsuc i)).
  quantifier : (F → O i) → O (lsuc i)
  quantifier = for-all

  -- The decoding at an ordinary family of codes, both ways.
  holds-everywhere : (g : Q) → El (for-all g) → (x : F) → El (g x)
  holds-everywhere = decode-all

  from-everywhere : (g : Q) → ((x : F) → El (g x)) → El (for-all g)
  from-everywhere = encode-all

  everywhere-is-equiv : (g : Q) → IsEquiv (decode-all g)
  everywhere-is-equiv = decode-all-equiv

  -- The three steps separately, with the orientation: the fibre of the
  -- point stores a path FROM v; the middle type has a path TO v.
  stored : (g : Q) → Fiber point g → v ≡ g
  stored g z = snd z

  reversed : (g : Q) (z : Fiber point g) → fibre-to-path g z ≡ sym (stored g z)
  reversed g z = refl

  -- The quantifier of the constantly true family is true, and so its
  -- decoded proposition holds.
  truth : for-all v ≡ top
  truth = for-all-top

  -- A family that holds everywhere is the constantly true family.
  constant : (g : Q) → ((x : F) → El (g x)) → g ≡ v
  constant = pointwise-to-path

------------------------------------------------------------------------
-- 2. Over the one-point type the quantifier is the code at the point.

module OverOnePoint {@♭ i : Level}
  (@♭ sQ : ShapeData (CrispUnitAt (lsuc i) → O i))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (fe-ji : FunExt₂ (lsuc i) i) where

  open Quantifier unit-at-discrete sQ fe-i pe-i fe-j
  open Decoding fe-ji

  at-the-point : (g : Q) → El (for-all g) → El (g end-at)
  at-the-point g z = decode-all g z end-at

  private
    everywhere : (g : Q) → El (g end-at) → (x : CrispUnitAt (lsuc i)) → El (g x)
    everywhere g y end-at = y

  from-the-point : (g : Q) → El (g end-at) → El (for-all g)
  from-the-point g y = encode-all g (everywhere g y)

  -- Both types are propositions.
  one-point-equiv : (g : Q) → IsEquiv (at-the-point g)
  one-point-equiv g =
    prop-equiv (El-is-prop (for-all g)) (El-is-prop (g end-at))
      (at-the-point g) (from-the-point g)

------------------------------------------------------------------------
-- 3. Over the two-point type it is the binary meet of two codes: a
--    bounded meet, obtained without any operation on O i.

-- The index type and its discreteness are defined outside the module
-- that has the ordinary parameter fe-ji: a definition of a module with an
-- ordinary parameter is not a crisp term inside that module, and the
-- quantifier takes its index type and its discreteness crisply.
Two : (@♭ i : Level) → Set (lsuc i)
Two i = CrispUnitAt (lsuc i) ⊎ CrispUnitAt (lsuc i)

two-discrete : {@♭ i : Level} → Discrete (Two i)
two-discrete = sum-discrete unit-at-discrete unit-at-discrete

module OverTwoPoints {@♭ i : Level}
  (@♭ sQ : ShapeData (Two i → O i))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (fe-ji : FunExt₂ (lsuc i) i) where

  open Quantifier two-discrete sQ fe-i pe-i fe-j
  open Decoding fe-ji

  -- The family with the two given values.
  pair-of : O i → O i → Q
  pair-of a b (inl _) = a
  pair-of a b (inr _) = b

  meet : O i → O i → O (lsuc i)
  meet a b = for-all (pair-of a b)

  meet-out : (a b : O i) → El (meet a b) → El a × El b
  meet-out a b z =
    decode-all (pair-of a b) z (inl end-at) ,
    decode-all (pair-of a b) z (inr end-at)

  private
    both : (a b : O i) → El a × El b → (x : Two i) → El (pair-of a b x)
    both a b t (inl _) = fst t
    both a b t (inr _) = snd t

  meet-in : (a b : O i) → El a × El b → El (meet a b)
  meet-in a b t = encode-all (pair-of a b) (both a b t)

  meet-equiv : (a b : O i) → IsEquiv (meet-out a b)
  meet-equiv a b =
    prop-equiv (El-is-prop (meet a b)) product-is-prop
      (meet-out a b) (meet-in a b)
    where
    product-is-prop : IsProp (El a × El b)
    product-is-prop t t′ =
      pair-path (El-is-prop a (fst t) (fst t′)) (El-is-prop b (snd t) (snd t′))
