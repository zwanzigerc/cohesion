{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The support of the principal filter in use: the carriers do not change
-- when the hypotheses arrive. Claude (Fable), 14 November 2026;
-- fable-impl-20 (HANDOFF-36, the bounded client of section 2).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters, all crisp: a type S₀ : Set (lsuc i)
-- and a map η₀ : ♯ (O i) → S₀, as a bare carrier and unit; proofs that S₀
-- is a discrete set; ONE shape datum sQ of the power Q; fe-i, pe-i, fe-j.
module PrincipalSupportExamples where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import BaseClassifier hiding (C)
open import PrincipalSupport

module Generic {@♭ i : Level}
  {@♭ S₀ : Set (lsuc i)} (@♭ η₀ : ♯ (O i) → S₀)
  (@♭ S₀-set : IsSet S₀) (@♭ S₀-discrete : Discrete S₀)
  (@♭ sQ : ShapeData (Carrier.Q S₀ η₀))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) where

  -- Formed from S₀ and η₀ alone.
  module Before = Carrier S₀ η₀

  open Facts η₀ S₀-set S₀-discrete sQ fe-i pe-i fe-j

  ----------------------------------------------------------------------
  -- 1. The carriers after the hypotheses are the carriers before them,
  --    and they are the expressions of the handoff. All by computation.

  same-fibre : F ≡ Before.F
  same-fibre = refl

  fibre-is : F ≡ Fiber (λ q → η₀ (sharp-unit q)) (η₀ (sharp-unit top))
  fibre-is = refl

  same-power : Q ≡ Before.Q
  same-power = refl

  power-is : Q ≡ (F → O i)
  power-is = refl

  same-support : P ≡ Before.P
  same-support = refl

  -- The support is the identity type of the two maps; it is not a decoded
  -- code.
  support-is : P ≡ (fst {B = λ q → e₀ q ≡ e₀ top} ≡ (λ _ → top))
  support-is = refl

  ----------------------------------------------------------------------
  -- 2. What the hypotheses add.

  -- The top code is in its own class: a point of F.
  top-point : F
  top-point = top , refl

  support-discrete : Discrete P
  support-discrete = P-discrete

  support-is-prop : IsProp P
  support-is-prop = P-is-prop

  -- The code of the support, one level up, and its decoding both ways.
  code-of-support : O (lsuc i)
  code-of-support = p

  decoded : El p → P
  decoded = p-to-P

  encoded : P → El p
  encoded = P-to-p

  decoding-is-equiv : IsEquiv p-to-P
  decoding-is-equiv = p-equiv

  -- The lower bound, used at a point: under the support every code in the
  -- class of top holds.
  holds-under-support : P → (q : O i) → e₀ q ≡ e₀ top → El q
  holds-under-support e q h = lower-bound e (q , h)

  -- And through the code: a point of El p gives the same.
  holds-under-code : El p → (x : F) → El (u x)
  holds-under-code z = lower-bound (p-to-P z)
