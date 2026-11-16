{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The second fixed power, the closed carrier and its split retraction in
-- use. Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, the
-- bounded clients of sections 3 and 4).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters, all crisp:
--   section 1   a discrete P : Set (lsuc i); ONE shape datum sR of the
--               power P → O (lsuc i); fe-j, pe-j, fe-jk. No truncation.
--   section 2   in addition a truncation structure tau of level lsuc i
--   section 3   a truncation structure and two discrete types, alone
-- The truncation structure is a parameter throughout: no truncation is
-- constructed, and no point of one is opened to choose a summand.
module ClosedCarrierExamples where

open import Foundations
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂; Truncation)
open import SmallPropositions
open import BaseClassifier hiding (C)
open import TruncationDiscrete
import ClosedCarrier
import JoinRetraction

------------------------------------------------------------------------
-- 1. The second power and the equality-fibre carrier.

module SecondPower {@♭ i : Level} {@♭ P : Set (lsuc i)}
  (@♭ P-discrete : Discrete P)
  (@♭ sR : ShapeData (P → O (lsuc i)))
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i))) where

  -- Formed from P alone.
  module Before = ClosedCarrier.Carrier P

  open ClosedCarrier.Facts P-discrete sR fe-j pe-j fe-jk

  -- The carriers are those, and C is the equality fibre. By computation.
  same-power : R ≡ Before.R
  same-power = refl

  same-carrier : C ≡ Before.C
  same-carrier = refl

  carrier-is : C ≡ Fiber (λ (q : O (lsuc i)) (_ : P) → q) (λ _ → top)
  carrier-is = refl

  -- The index P is of Set (lsuc i) and the target of Set (lsuc (lsuc i)):
  -- the power and the carrier are one universe above P.
  power-level : Set (lsuc (lsuc i))
  power-level = R

  power-discrete : Discrete R
  power-discrete = R-discrete

  carrier-discrete : Discrete C
  carrier-discrete = C-discrete

  carrier-set : IsSet C
  carrier-set = C-set

  -- The comparison with the pairs of a code and an implication, used in
  -- both directions.
  from-implication : (q : O (lsuc i)) → (P → El q) → C
  from-implication q h = unpresent (q , h)

  to-implication : (c : C) → P → El (inclusion c)
  to-implication c = snd (present c)

  comparison : IsEquiv present
  comparison = present-is-equiv

  -- A code that holds is in the closed carrier, whatever P is.
  from-truth : (q : O (lsuc i)) → El q → C
  from-truth q y = from-implication q (λ _ → y)

  -- Two points with the same code are equal.
  same-code : (c c′ : C) → inclusion c ≡ inclusion c′ → c ≡ c′
  same-code = inclusion-injective

------------------------------------------------------------------------
-- 2. The join and the split retraction.

module Split {@♭ i : Level} {@♭ P : Set (lsuc i)}
  (@♭ P-discrete : Discrete P)
  (@♭ sR : ShapeData (P → O (lsuc i)))
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ tau : Truncation (lsuc i)) where

  -- The join is made from P-discrete and tau alone.
  module Before = JoinRetraction.Join P-discrete tau

  open JoinRetraction.Retraction P-discrete sR fe-j pe-j fe-jk tau
  open Truncation tau

  same-join : joinP ≡ Before.joinP
  same-join = refl

  -- Its target is the classifier of the SAME level.
  join : O (lsuc i) → O (lsuc i)
  join = joinP

  -- The decoding at an ordinary code: a point of the truncation, not a
  -- chosen summand.
  merely-either : (q : O (lsuc i)) → El (joinP q) → ∥ P ⊎ El q ∥
  merely-either = join-decode

  -- The retraction and the split law.
  onto : O (lsuc i) → C
  onto = closed-retraction

  split : (c : C) → closed-retraction (inclusion c) ≡ c
  split = retracts

  -- Consequences, all pointwise. The join fixes the codes of the closed
  -- carrier, top among them, and it is idempotent.
  fixes-closed : (c : C) → joinP (inclusion c) ≡ inclusion c
  fixes-closed = absorb

  fixes-top : joinP top ≡ top
  fixes-top = absorb truth-point

  idempotent : (q : O (lsuc i)) → joinP (joinP q) ≡ joinP q
  idempotent q = absorb (closed-retraction q)

  -- A code is in the image of the inclusion exactly when the join fixes
  -- it; the forward direction with the point as a witness.
  in-image : (q : O (lsuc i)) → joinP q ≡ q → Fiber inclusion q
  in-image q e = closed-retraction q , e

  -- Under P every code of the closed carrier holds.
  holds-under : (c : C) → P → El (inclusion c)
  holds-under c = implication (inclusion c) (snd c)

------------------------------------------------------------------------
-- 3. The two discreteness lemmas alone: no extensionality, no shape.

module Lemmas {@♭ ℓ : Level} (@♭ tau : Truncation ℓ)
  {@♭ A B : Set ℓ} (@♭ dA : Discrete A) (@♭ dB : Discrete B) where

  open Truncation tau

  sum : Discrete (A ⊎ B)
  sum = sum-discrete dA dB

  truncated : Discrete ∥ A ∥
  truncated = truncation-discrete tau dA

  truncated-sum : Discrete ∥ A ⊎ B ∥
  truncated-sum = truncation-discrete tau sum
