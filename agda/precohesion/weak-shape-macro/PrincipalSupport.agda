{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The support of the principal filter, as an equality type that is fixed
-- BEFORE any extensionality hypothesis, and its code.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, section 2;
-- BASE-CLASSIFIER-BOUNDED-MEET-02, section 2).
--
-- Nothing is postulated and nothing is declared.
--
-- LEVELS. i crisp, j = lsuc i. The given carrier S₀ : Set j and unit
-- η₀ : ♯ (O i) → S₀ are those of one chosen shape of ♯ (O i). Here they are
-- a bare type and a bare map: this module asks no universal property.
--
-- Carrier (S₀ and η₀ only; no hypothesis):
--   e₀ q = η₀ (sharp-unit q) : O i → S₀
--   F = Fiber e₀ (e₀ top) : Set j         the codes in the class of top
--   u = fst : F → O i
--   Q = F → O i,  v = λ _ → top           BoundedQuantifier.Carrier at F
--   P = (u ≡ v) : Set j                   the support
-- These are the types of the handoff as they stand. In particular P is
-- the identity type u ≡ v of the function type Q; it is NOT defined as a
-- decoded code, and Facts below proves El p ≃ P as a theorem.
--
-- Discreteness (η₀ and crisp S₀-discrete; still no extensionality):
--   F-discrete            a fibre over a crisp point of a crisp map of
--                         discrete types (ShapeElim.FiberDiscrete)
--
-- Facts (η₀, crisp S₀-set, S₀-discrete, sQ : ShapeData Q, fe-i, pe-i,
-- fe-j):
--   F-set                 Σ of a set and of identity types of a set
--   the whole of BoundedQuantifier.Quantifier at F, re-exported
--   P-discrete            an identity type of the discrete type Q at two
--                         crisp points (DiscretePullback.identity-discrete)
--   P-is-prop             Q is a set
--   p = for-all u : O j   defined AFTER the hypotheses
--   p-equiv               El p ≃ P, maps both ways with both inverse laws
--   lower-bound           P → (x : F) → El (u x)
--
-- WHAT IS NOT HERE. That p is in the class of top at the NEXT level, that
-- is eⱼ p ≡ eⱼ top for the unit of a shape of ♯ (O j), is the membership
-- equation; it needs the codiscrete power comparison and MonoC, and is
-- proved in PrincipalFilter. Nothing here says that P has a code in O i.
module PrincipalSupport where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import DiscretePullback using (identity-discrete)
open import ShapeElim using (module FiberDiscrete)
open import TotalBridge using (Σ-set)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import BaseClassifier
open import BaseClassifierLaws using (module Laws)
import BoundedQuantifier

------------------------------------------------------------------------
-- 1. The carriers. No hypothesis.

module Carrier {@♭ i : Level}
  (@♭ S₀ : Set (lsuc i)) (@♭ η₀ : ♯ (O i) → S₀) where

  e₀ : O i → S₀
  e₀ q = η₀ (sharp-unit q)

  F : Set (lsuc i)
  F = Fiber e₀ (e₀ top)

  u : F → O i
  u = fst

  open BoundedQuantifier.Carrier F public

  P : Set (lsuc i)
  P = u ≡ v

------------------------------------------------------------------------
-- 2. F is discrete. No extensionality.

module Discreteness {@♭ i : Level}
  {@♭ S₀ : Set (lsuc i)} (@♭ η₀ : ♯ (O i) → S₀)
  (@♭ S₀-discrete : Discrete S₀) where

  open Carrier S₀ η₀ public

  F-discrete : Discrete F
  F-discrete = FiberDiscrete.discrete S₀-discrete O-discrete e₀ (e₀ top)

------------------------------------------------------------------------
-- 3. Sethood, the quantifier at F, and the code of the support.

module Facts {@♭ i : Level}
  {@♭ S₀ : Set (lsuc i)} (@♭ η₀ : ♯ (O i) → S₀)
  (@♭ S₀-set : IsSet S₀) (@♭ S₀-discrete : Discrete S₀)
  (@♭ sQ : ShapeData (Carrier.Q S₀ η₀))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) where

  open Discreteness η₀ S₀-discrete public

  private
    module Li = Laws fe-i pe-i

  F-set : IsSet F
  F-set = Σ-set Li.O-is-set (λ q → prop-is-set (S₀-set (e₀ q) (e₀ top)))

  -- Q-discrete, Q-set, for-all and its comparisons, at this F.
  open BoundedQuantifier.Quantifier F-discrete sQ fe-i pe-i fe-j public
    hiding (Q; v; One; point)

  P-discrete : Discrete P
  P-discrete = identity-discrete Q-discrete u v

  P-is-prop : IsProp P
  P-is-prop = Q-set u v

  -- The code of the support. Its type O j does not mention P.
  p : O (lsuc i)
  p = for-all u

  p-to-P : El p → P
  p-to-P z = fibre-to-path u (code-to-fibre u z)

  P-to-p : P → El p
  P-to-p e = fibre-to-code u (path-to-fibre u e)

  p-equiv : IsEquiv p-to-P
  p-equiv = prop-equiv (El-is-prop p) P-is-prop p-to-P P-to-p

  -- What the open argument needs: under P every code of F holds.
  lower-bound : P → (x : F) → El (u x)
  lower-bound = path-to-pointwise u
