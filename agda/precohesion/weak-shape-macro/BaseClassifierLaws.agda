{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The laws of the base classifier under two hypotheses: it is a set, two
-- CRISP codes with crisp implications both ways are equal, and the fibre
-- of truth over r is El r. Claude (Fable), 14 November 2026; fable-impl-19
-- (HANDOFF-35, item 2; BASE-CLASSIFIER-NATIVE-AUDIT-01, sections 2, 8.3).
--
-- Nothing is postulated. The two hypotheses are CRISP module parameters:
--   fe : FunExt₂ i i   function extensionality at the level of the
--                      propositions (GlobalPropositions.FunExt₂);
--   pe : PropExt i     propositional extensionality for the ORDINARY
--                      propositions of level i (SmallPropositions.PropExt):
--                      the type is  {P Q : Set i} → IsProp P → IsProp Q
--                      → (P → Q) → (Q → P) → P ≡ Q,  with P, Q and the
--                      two implications ordinary variables. Only the proof
--                      pe itself is crisp.
-- They are crisp because their values end up under box: a path of codes is
-- made from a crisp path of propositions by box-crisp-path, twice.
--
-- The carrier, the decoding and the truth point are those of
-- BaseClassifier, defined before these hypotheses. This module defines no
-- carrier and re-exports none; every statement below mentions O, El and
-- top of BaseClassifier themselves.
--
-- What is NOT here. Code extensionality is for CRISP codes and CRISP
-- implications. For two ordinary codes r, s and ordinary maps
-- El r → El s, El s → El r this module gives nothing: an ordinary
-- implication cannot be boxed. (The truth fibre below is the one case
-- treated for an ordinary code, through the stored discreteness.) No
-- univalence and no higher statement is claimed.
module BaseClassifierLaws where

open import Foundations
open import CaptureContext using (CrispUnitAt; end-at)
open import NativeSharp using (box-crisp-path; transport)
open import NativeFlatIdentity using (flat-set)
open import GlobalPropositions using (FunExt₂; equiv-is-prop)
open import TotalBridge using (Σ-set)
open import SmallPropositions
open import SmallPropositionLaws using (hprop-ext; HProp-is-set)
open import BaseClassifier

module Laws {@♭ i : Level} (@♭ fe : FunExt₂ i i) (@♭ pe : PropExt i) where

  ----------------------------------------------------------------------
  -- 1. Sethood. HProp i is a set (FE and PE); ♭ of a set is a set
  --    (NativeFlatIdentity); d is proposition-valued (FE); a Σ of
  --    propositions over a set is a set; ♭ again.

  U-is-set : IsSet (U i)
  U-is-set = flat-set (HProp-is-set fe pe)

  d-is-prop : (q : U i) → IsProp (d q)
  d-is-prop (box (P , h)) = equiv-is-prop fe counit

  C-is-set : IsSet (C i)
  C-is-set = Σ-set U-is-set (λ q → prop-is-set (d-is-prop q))

  O-is-set : IsSet (O i)
  O-is-set = flat-set C-is-set

  ----------------------------------------------------------------------
  -- 2. Code extensionality, for crisp codes and crisp implications.

  code-ext : (@♭ r s : O i) (@♭ f : El r → El s) (@♭ g : El s → El r)
           → r ≡ s
  code-ext (box (box (P , h) , dP)) (box (box (Q , k) , dQ)) f g =
    box-crisp-path in-C
    where
    in-HProp : (P , h) ≡ (Q , k)
    in-HProp = hprop-ext fe pe f g

    in-C : (box (P , h) , dP) ≡ (box (Q , k) , dQ)
    in-C = subtype-path d-is-prop (box-crisp-path in-HProp)

  ----------------------------------------------------------------------
  -- 3. The fibre of truth: (r ≡ top) ≃ El r, for an ORDINARY r.
  --    The identity type is of Set (lsuc i) and El r of Set i; the
  --    equivalence is between these two types as they are.

  -- Transport of the point of the unit.
  truth-out : (r : O i) → r ≡ top → El r
  truth-out r e = transport El (sym e) end-at

  -- An ordinary p : P is first made a point of ♭ P by the stored
  -- discreteness, and only then, as a crisp point, turned into a crisp
  -- implication.
  truth-in : (r : O i) → El r → r ≡ top
  truth-in (box (box (P , h) , dP)) p = at-flat (inverse dP p)
    where
    at-flat : ♭ P → code P h dP ≡ top
    at-flat (box x) = code-ext (code P h dP) top (λ _ → end-at) (λ _ → x)

  -- Both sides are propositions. The inverse is truth-in by computation.
  truth-fibre : (r : O i) → IsEquiv (truth-out r)
  truth-fibre r =
    prop-equiv (O-is-set r top) (El-is-prop r) (truth-out r) (truth-in r)
