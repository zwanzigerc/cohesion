{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The join with a fixed proposition, as a whole map of the base
-- classifier, and the split retraction of the closed carrier onto it.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, section 4;
-- BASE-CLASSIFIER-BOUNDED-MEET-02, section 4; NEXT-AFTER-M19-SLICE-01,
-- addendum).
--
-- Nothing is postulated and nothing is declared.
--
-- LEVELS. i crisp, j = lsuc i, k = lsuc j. P : Set j is ONE fixed crisp
-- discrete type, as in ClosedCarrier.
--
-- THE TRUNCATION IS SUPPLIED. tau : GlobalPropositions.Truncation j is a
-- crisp record of Set k whose carriers are in Set j, with a recursor into
-- propositions of Set j and no computation rule. It is not made from a
-- shape and it is not constructed here. Its points are never opened to
-- choose a summand: every map out of ∥ P ⊎ El q ∥ below goes into a
-- proposition, by the recursor of tau.
--
-- Join (crisp P-discrete and tau; NO extensionality):
--   join-at q             for a CRISP q : O j, the code of ∥ P ⊎ El q ∥.
--                         The decoded proposition of a crisp code is
--                         discrete (BaseClassifier.El-discrete), a sum of
--                         discrete types is discrete and so is its
--                         truncation (TruncationDiscrete). The code is of
--                         level j: the target is O j, not O k.
--   joinP : O j → O j     its extension to all q by induction on the
--                         discrete type O j
--   joinP-β               the computation rule at a crisp q, a path
--   join-equiv            El (joinP q) ≃ ∥ P ⊎ El q ∥ for an ORDINARY q,
--                         maps both ways with both inverse laws
--   left, right           P → El (joinP q) and El q → El (joinP q)
--
-- Retraction (in addition crisp sR, fe-j, pe-j, fe-jk: the data of
-- ClosedCarrier.Facts, which is opened here):
--   closed-retraction : O j → C
--                         q ↦ (joinP q , the path that left gives)
--   absorb                joinP (inclusion c) ≡ inclusion c for every
--                         ORDINARY c : C
--   retracts              closed-retraction (inclusion c) ≡ c for every
--                         ordinary c: the pointwise split law
--   closed-retraction-top closed-retraction top ≡ truth-point
-- (Foundations.retraction is the name of a law of an equivalence; hence
-- the longer name.)
--
-- HOW absorb IS PROVED. At a CRISP c the stored path snd c is crisp, so
-- it gives a crisp map P → El (inclusion c). With the recursor of tau
-- this is a crisp implication ∥ P ⊎ El q ∥ → El q; the right injection is
-- a crisp implication back. Crisp code extensionality of level j
-- (BaseClassifierLaws.code-ext) identifies the two CRISP codes. Induction
-- on the discrete type C gives every ordinary c. Code extensionality is
-- applied to crisp data only; no rule for ordinary codes is used.
--
-- The second components of the two points of C lie in a proposition, so
-- the split law follows from absorb. No equality of whole functions with
-- domain and codomain in Set k is stated, and FunExt₂ k k is not asked.
module JoinRetraction where

open import Foundations
open import NativeSharp using (transport)
open import GlobalPrecohesion
  using (ShapeData; discrete-elim; discrete-elim-β)
open import GlobalPropositions using (FunExt₂; Truncation)
open import SmallPropositions
open import BaseClassifier hiding (C)
open import BaseClassifierLaws using (module Laws)
open import TruncationDiscrete
import ClosedCarrier

------------------------------------------------------------------------
-- 1. The join. No extensionality.

module Join {@♭ i : Level} {@♭ P : Set (lsuc i)}
  (@♭ P-discrete : Discrete P)
  (@♭ tau : Truncation (lsuc i)) where

  open Truncation tau

  JoinType : O (lsuc i) → Set (lsuc i)
  JoinType q = ∥ P ⊎ El q ∥

  join-discrete : (@♭ q : O (lsuc i)) → Discrete (JoinType q)
  join-discrete q =
    truncation-discrete tau (sum-discrete P-discrete (El-discrete q))

  join-at : (@♭ q : O (lsuc i)) → O (lsuc i)
  join-at q = code (JoinType q) squash (join-discrete q)

  joinP : O (lsuc i) → O (lsuc i)
  joinP = discrete-elim O-discrete (λ _ → O (lsuc i)) join-at

  joinP-β : (@♭ q : O (lsuc i)) → joinP q ≡ join-at q
  joinP-β = discrete-elim-β O-discrete (λ _ → O (lsuc i)) join-at

  -- El (join-at q) is JoinType q by computation. At a crisp q the two maps
  -- are transports along joinP-β; induction on O j gives every q.
  Comparison : O (lsuc i) → Set (lsuc i)
  Comparison q = (El (joinP q) → JoinType q) × (JoinType q → El (joinP q))

  private
    comparison-at : (@♭ q : O (lsuc i)) → Comparison q
    comparison-at q =
      transport El (joinP-β q) , transport El (sym (joinP-β q))

  comparison : (q : O (lsuc i)) → Comparison q
  comparison = discrete-elim O-discrete Comparison comparison-at

  join-decode : (q : O (lsuc i)) → El (joinP q) → JoinType q
  join-decode q = fst (comparison q)

  join-encode : (q : O (lsuc i)) → JoinType q → El (joinP q)
  join-encode q = snd (comparison q)

  -- Both sides are propositions.
  join-equiv : (q : O (lsuc i)) → IsEquiv (join-decode q)
  join-equiv q =
    prop-equiv (El-is-prop (joinP q)) squash (join-decode q) (join-encode q)

  left : (q : O (lsuc i)) → P → El (joinP q)
  left q z = join-encode q ∣ inl z ∣

  right : (q : O (lsuc i)) → El q → El (joinP q)
  right q y = join-encode q ∣ inr y ∣

------------------------------------------------------------------------
-- 2. The retraction of the closed carrier.

module Retraction {@♭ i : Level} {@♭ P : Set (lsuc i)}
  (@♭ P-discrete : Discrete P)
  (@♭ sR : ShapeData (P → O (lsuc i)))
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ tau : Truncation (lsuc i)) where

  open ClosedCarrier.Facts P-discrete sR fe-j pe-j fe-jk public
  open Join P-discrete tau public

  private
    module Lj = Laws fe-j pe-j
    open Truncation tau

  -- The left injection makes joinP q hold under P; that is a path
  -- const (joinP q) ≡ w.
  closed-retraction : O (lsuc i) → C
  closed-retraction q = joinP q , path-from (joinP q) (left q)

  closed-retraction-inclusion :
    (q : O (lsuc i)) → inclusion (closed-retraction q) ≡ joinP q
  closed-retraction-inclusion q = refl

  private
    -- At a crisp c. The sum is an ordinary argument and is matched; c is
    -- not matched, its two projections are crisp terms.
    collapse : (@♭ c : C) → P ⊎ El (inclusion c) → El (inclusion c)
    collapse c (inl z) = implication (inclusion c) (snd c) z
    collapse c (inr y) = y

    absorb-at : (@♭ c : C) → joinP (inclusion c) ≡ inclusion c
    absorb-at c =
      joinP-β (inclusion c)
      ∙ Lj.code-ext (join-at (inclusion c)) (inclusion c)
          (∥-rec (El-is-prop (inclusion c)) (collapse c))
          (λ y → ∣ inr y ∣)

  absorb : (c : C) → joinP (inclusion c) ≡ inclusion c
  absorb =
    discrete-elim C-discrete (λ c → joinP (inclusion c) ≡ inclusion c)
      absorb-at

  -- The split law, pointwise.
  retracts : (c : C) → closed-retraction (inclusion c) ≡ c
  retracts c = subtype-path path-is-prop (absorb c)

  -- inclusion truth-point is top by computation.
  closed-retraction-top : closed-retraction top ≡ truth-point
  closed-retraction-top = retracts truth-point
