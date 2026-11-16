{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The action of T = shape ∘ ♯ on the bounded quantifier, with its unit
-- law: a map from a fixed shape of ♯ Q to a fixed shape of ♯ (O j), one
-- universe higher. Claude (Fable), 14 November 2026; fable-impl-20
-- (HANDOFF-36, section 5; BASE-CLASSIFIER-BOUNDED-MEET-02, section 2,
-- equation (2); NEXT-AFTER-M19-SLICE-01, item 4).
--
-- Nothing is postulated and nothing is declared. The map is the canonical
-- one that LargeTarget.SharpComposite already defines; this module only
-- instantiates it at for-all.
--
-- LEVELS. i crisp, j = lsuc i, k = lsuc j. Q = F → O i : Set j, and
-- for-all : Q → O j with O j : Set k.
--
-- DATA, all crisp, beyond those of BoundedQuantifier.Quantifier:
--   SQ : Set j,  etaQ : ♯ Q → SQ      the carrier and the unit of ONE
--                                     chosen shape of ♯ Q
--   cQ : LargeTerminalUP k (♯ Q) SQ etaQ
--                                     a certificate that THIS carrier and
--                                     unit eliminate into discrete sets of
--                                     Set k. For a shape datum sY of ♯ Q
--                                     this type is LargeOn k sY.
--   Sj : Set k, with Sj-set and Sj-discrete,  etaj : ♯ (O j) → Sj
--                                     the carrier and the unit of one
--                                     chosen shape of ♯ (O j)
--
-- EXPORTS.
--   T-for-all : SQ → Sj
--   T-for-all-unit g : T-for-all (etaQ (sharp-unit g))
--                      ≡ etaj (sharp-unit (for-all g))    for ORDINARY g
--
-- WHICH SHAPES. The datum sQ : ShapeData Q of BoundedQuantifier is a shape
-- of Q; it proves Q discrete. SQ and etaQ belong to a shape of ♯ Q, which
-- is another type, and the certificate cQ is about SQ and etaQ. Nothing
-- here relates the two, and neither is made from the other.
--
-- Sj and etaj are taken as a bare carrier and unit, with sethood and
-- discreteness: that is all the map and its law use. A client that goes
-- on to use the recursor of that shape supplies a shape datum of ♯ (O j)
-- and instantiates Sj and etaj by ITS carrier and unit (PrincipalFilter
-- does so); this module does not choose one.
--
-- No extensionality beyond the three hypotheses of Quantifier: the unit
-- law is the computation rule of the certificate and sharp-map-unit.
-- FunExt₂ k k is not asked.
module QuantifierShape where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import LargeTarget using (LargeTerminalUP; module SharpComposite)
open import BaseClassifier hiding (C)
import BoundedQuantifier

module Naturality {@♭ i : Level} {@♭ F : Set (lsuc i)}
  (@♭ dF : Discrete F)
  (@♭ sQ : ShapeData (F → O i))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  {@♭ SQ : Set (lsuc i)} {@♭ etaQ : ♯ (F → O i) → SQ}
  (@♭ cQ : LargeTerminalUP (lsuc (lsuc i)) (♯ (F → O i)) SQ etaQ)
  (@♭ Sj : Set (lsuc (lsuc i)))
  (@♭ Sj-set : IsSet Sj) (@♭ Sj-discrete : Discrete Sj)
  (@♭ etaj : ♯ (O (lsuc i)) → Sj) where

  open BoundedQuantifier.Quantifier dF sQ fe-i pe-i fe-j using (Q; for-all)

  private
    module Composite =
      SharpComposite (lsuc (lsuc i)) cQ Sj Sj-set Sj-discrete etaj for-all

  T-for-all : SQ → Sj
  T-for-all = Composite.T-map

  T-for-all-unit : (g : Q)
                 → T-for-all (etaQ (sharp-unit g))
                   ≡ etaj (sharp-unit (for-all g))
  T-for-all-unit = Composite.T-natural
