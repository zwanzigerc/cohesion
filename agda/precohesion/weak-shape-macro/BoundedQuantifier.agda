{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The bounded universal quantifier over one fixed discrete type: the
-- characteristic map of the point "constantly true" of a fixed power of
-- the base classifier. Claude (Fable), 14 November 2026; fable-impl-20
-- (HANDOFF-36, section 1; BASE-CLASSIFIER-BOUNDED-MEET-02, section 1).
--
-- Nothing is postulated and nothing is declared. A conditional
-- construction of the library, not a theorem of the paper.
--
-- LEVELS. i is a crisp level; write j = lsuc i. F : Set j is ONE fixed
-- crisp type. O i : Set j is the base classifier of level i and O j its
-- successor (BaseClassifier). Agda is not cumulative, and nothing here is
-- raised or lowered.
--
-- Carrier (no hypothesis at all, not even discreteness of F):
--   Q = F → O i : Set j        v = λ _ → top : Q
--   One = CrispUnitAt j        point : One → Q,  point _ = v
--
-- Quantifier. Data, all crisp:
--   dF   : Discrete F
--   sQ   : ShapeData Q          ONE supplied shape datum of the power. It
--                               serves to prove Q discrete and nothing
--                               else; it is not made here, and it is not a
--                               shape datum of ♯ Q.
--   fe-i : FunExt₂ i i, pe-i : PropExt i     O i is a set; its truth fibre
--   fe-j : FunExt₂ j j        the retract law of the power; paths of
--                             functions F → O i from pointwise ones
--   Q-discrete, Q-set     FixedPower.Power at index level j and c = lzero,
--                         as it is; its module is re-exported as QPower
--                         (evaluate, evaluate-η, retraction-law)
--   for-all : Q → O j     the characteristic map of the whole crisp mono
--                         point (MonoClassifier.Characteristic at level j)
-- and, for an ORDINARY g : Q, maps both ways with both inverse laws:
--   code-fibre-equiv      El (for-all g) ≃ Fiber point g
--   fibre-path-equiv      Fiber point g ≃ (g ≡ v)
-- and the two maps of the third comparison and of the composite:
--   path-to-pointwise, pointwise-to-path;  decode-all, encode-all
--
-- Decoding (one more hypothesis, fe-ji : FunExt₂ j i, ORDINARY): the
-- inverse laws of those maps.
--   path-pointwise-equiv  (g ≡ v) ≃ ((x : F) → El (g x))
--   decode-all-equiv      El (for-all g) ≃ ((x : F) → El (g x))
--
-- Truth (one more hypothesis, crisp pe-j : PropExt j):
--   for-all-top           for-all v ≡ top
--
-- ORIENTATION. A point of Fiber point g is a pair (x , e) with
-- e : point x ≡ g, and point x is v by computation: the stored path goes
-- FROM v TO g. fibre-to-path reverses it, so that the path of the middle
-- type goes from g to v, the direction in which happly and the truth
-- fibre of level i are applied.
--
-- INVERSE LAWS. Each of the four types is a proposition: El (for-all g)
-- by its code; Fiber point g because Q is a set and One a proposition;
-- g ≡ v because Q is a set; the function type by fe-ji. So each pair of
-- maps is an equivalence (SmallPropositions.prop-equiv), and no
-- computation rule of function extensionality is used or assumed.
--
-- WHAT IS NOT HERE. for-all is defined on this ONE power. There is no
-- family of quantifiers indexed by a type variable, no quantifier over an
-- ordinary family, and no shape datum is requested for a fibre of a family
-- over Q. The comparisons are for an ordinary g, but for-all itself is
-- the classifier of one whole crisp mono. Nothing is said about ♯ Q here;
-- QuantifierShape is about that.
module BoundedQuantifier where

open import Foundations
open import CaptureContext using (CrispUnitAt; end-at; unit-at-discrete)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import SmallPropositionLaws using (pi-is-prop)
open import BaseClassifier
open import BaseClassifierLaws using (module Laws)
open import MonoClassifier using (module Characteristic)
import FixedPower

------------------------------------------------------------------------
-- 1. The carriers. No hypothesis.

module Carrier {@♭ i : Level} (@♭ F : Set (lsuc i)) where

  Q : Set (lsuc i)
  Q = F → O i

  v : Q
  v _ = top

  One : Set (lsuc i)
  One = CrispUnitAt (lsuc i)

  point : One → Q
  point _ = v

------------------------------------------------------------------------
-- 2. The quantifier.

module Quantifier {@♭ i : Level} {@♭ F : Set (lsuc i)}
  (@♭ dF : Discrete F)
  (@♭ sQ : ShapeData (F → O i))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) where

  open Carrier F public

  private
    module Li = Laws fe-i pe-i

  -- The fixed power, as FixedPower proves it: index level j, c = lzero.
  module QPower = FixedPower.Power lzero dF Li.O-is-set O-discrete sQ fe-j

  Q-discrete : Discrete Q
  Q-discrete = QPower.fixed-power-discrete

  Q-set : IsSet Q
  Q-set = QPower.fixed-power-set

  -- The point is a mono: its target is a set and its source a proposition.
  point-mono : (g : Q) → IsProp (Fiber point g)
  point-mono = injective-fibres point Q-set (λ x y _ → unit-at-is-prop x y)

  module Classifier =
    Characteristic Q-discrete unit-at-discrete point point-mono

  for-all : Q → O (lsuc i)
  for-all = Classifier.χ

  -- First comparison: the decoded code and the fibre of the point.
  code-to-fibre : (g : Q) → El (for-all g) → Fiber point g
  code-to-fibre = Classifier.to-fibre

  fibre-to-code : (g : Q) → Fiber point g → El (for-all g)
  fibre-to-code = Classifier.from-fibre

  code-fibre-equiv : (g : Q) → IsEquiv (code-to-fibre g)
  code-fibre-equiv = Classifier.fibre-equiv

  -- Second comparison: the stored path, reversed.
  fibre-to-path : (g : Q) → Fiber point g → g ≡ v
  fibre-to-path g z = sym (snd z)

  path-to-fibre : (g : Q) → g ≡ v → Fiber point g
  path-to-fibre g e = end-at , sym e

  fibre-path-equiv : (g : Q) → IsEquiv (fibre-to-path g)
  fibre-path-equiv g =
    prop-equiv (point-mono g) (Q-set g v) (fibre-to-path g) (path-to-fibre g)

  -- Third comparison, the two maps. v x is top by computation.
  path-to-pointwise : (g : Q) → g ≡ v → (x : F) → El (g x)
  path-to-pointwise g e x = Li.truth-out (g x) (happly e x)

  pointwise-to-path : (g : Q) → ((x : F) → El (g x)) → g ≡ v
  pointwise-to-path g h = fe-j (λ x → Li.truth-in (g x) (h x))

  -- The composites.
  decode-all : (g : Q) → El (for-all g) → (x : F) → El (g x)
  decode-all g z = path-to-pointwise g (fibre-to-path g (code-to-fibre g z))

  encode-all : (g : Q) → ((x : F) → El (g x)) → El (for-all g)
  encode-all g h = fibre-to-code g (path-to-fibre g (pointwise-to-path g h))

  ----------------------------------------------------------------------
  -- 3. The inverse laws of the third comparison. Functions from F : Set j
  --    into the decoded propositions of Set i: extensionality at exactly
  --    these two levels. Its only use is the propositionhood of the
  --    function type, so it is an ordinary argument.

  module Decoding (fe-ji : FunExt₂ (lsuc i) i) where

    pointwise-is-prop : (g : Q) → IsProp ((x : F) → El (g x))
    pointwise-is-prop g = pi-is-prop fe-ji (λ x → El-is-prop (g x))

    path-pointwise-equiv : (g : Q) → IsEquiv (path-to-pointwise g)
    path-pointwise-equiv g =
      prop-equiv (Q-set g v) (pointwise-is-prop g)
        (path-to-pointwise g) (pointwise-to-path g)

    decode-all-equiv : (g : Q) → IsEquiv (decode-all g)
    decode-all-equiv g =
      prop-equiv (El-is-prop (for-all g)) (pointwise-is-prop g)
        (decode-all g) (encode-all g)

  ----------------------------------------------------------------------
  -- 4. The quantifier of the constantly true family is true. The fibre of
  --    the point over v is inhabited, and an inhabited decoded code of
  --    level j is equal to top: the truth fibre of level j.

  module Truth (@♭ pe-j : PropExt (lsuc i)) where

    private
      module Lj = Laws fe-j pe-j

    for-all-top : for-all v ≡ top
    for-all-top = Lj.truth-in (for-all v) (fibre-to-code v (end-at , refl))
