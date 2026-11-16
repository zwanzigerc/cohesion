{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The carrier of the closed classifier of a fixed proposition, as an
-- equality fibre in a second fixed power.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, section 3;
-- BASE-CLASSIFIER-BOUNDED-MEET-02, section 3).
--
-- Nothing is postulated and nothing is declared.
--
-- LEVELS. i crisp, j = lsuc i, k = lsuc j. P : Set j is ONE fixed crisp
-- type; in the principal client it is the support of PrincipalSupport,
-- but this module does not know that. O j : Set k.
--
-- Carrier (P only; no hypothesis, not even discreteness of P):
--   R = P → O j : Set k          the second power
--   const : O j → R,  const q = λ _ → q
--   w = λ _ → top : R
--   C = Fiber const w : Set k    a code q with a path const q ≡ w
--   inclusion = fst : C → O j
--   truth-point = (top , refl) : C
-- C is DEFINED as this equality fibre. The type of pairs of a code and an
-- implication is Presentation below; that the two are equivalent is a
-- theorem of Facts, not a second definition and not a change of universe.
--
-- Facts. Data, all crisp:
--   P-discrete : Discrete P
--   sR   : ShapeData R          ONE supplied shape datum of the second
--                               power; it serves to prove R discrete. It
--                               is not a shape datum of ♯ R, and it is
--                               another datum than the one of the first
--                               power.
--   fe-j : FunExt₂ j j, pe-j : PropExt j     so that O j is a set
--   fe-jk : FunExt₂ j k                       functions P → O j
--   R-discrete, R-set     FixedPower.Power at index level j and c = k.
--                         The levels differ: P is in Set j, O j in Set k.
--                         FixedPower has that case (IndexedParameter);
--                         nothing is raised and Agda is not asked to be
--                         cumulative.
--   C-discrete, C-set
--   inclusion-injective, inclusion-mono       the inclusion is a mono
--   present-is-equiv      C ≃ Σ (q : O j). (P → El q)
--   present-truth         the truth point is sent to (top , λ _ → end-at)
--
-- The inverse laws of the last equivalence are identifications in
-- propositions: const q ≡ w because R is a set, and P → El q by fe-j. No
-- computation rule of extensionality is used.
--
-- WHAT IS NOT HERE. A retraction of the inclusion (JoinRetraction makes
-- one, from a supplied truncation), and the classifier theorem for the
-- closed restriction, which is not part of this increment.
module ClosedCarrier where

open import Foundations
open import CaptureContext using (end-at)
open import Adjointify using (quasi-inverse)
open import ShapeElim using (module FiberDiscrete)
open import TotalBridge using (Σ-set)
open import GlobalPrecohesion using (ShapeData)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions
open import SmallPropositionLaws using (pi-is-prop)
-- BaseClassifier.C, the type of codes with a proof of discreteness, is
-- another type than the C of this module and is not used here.
open import BaseClassifier hiding (C)
open import BaseClassifierLaws using (module Laws)
import FixedPower

------------------------------------------------------------------------
-- 1. The carriers. No hypothesis.

module Carrier {@♭ i : Level} (@♭ P : Set (lsuc i)) where

  R : Set (lsuc (lsuc i))
  R = P → O (lsuc i)

  const : O (lsuc i) → R
  const q _ = q

  w : R
  w _ = top

  C : Set (lsuc (lsuc i))
  C = Fiber const w

  inclusion : C → O (lsuc i)
  inclusion = fst

  -- const top is w by computation.
  truth-point : C
  truth-point = top , refl

  -- The other presentation: a code with an implication from P.
  Presentation : Set (lsuc (lsuc i))
  Presentation = Σ (O (lsuc i)) (λ q → P → El q)

------------------------------------------------------------------------
-- 2. The second power is a discrete set, and what follows for C.

module Facts {@♭ i : Level} {@♭ P : Set (lsuc i)}
  (@♭ P-discrete : Discrete P)
  (@♭ sR : ShapeData (P → O (lsuc i)))
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i))) where

  open Carrier P public

  private
    module Lj = Laws fe-j pe-j

  -- Index level j, c = k: the target O j is one universe above the index.
  module RPower =
    FixedPower.Power (lsuc (lsuc i)) P-discrete Lj.O-is-set O-discrete sR fe-jk

  R-discrete : Discrete R
  R-discrete = RPower.fixed-power-discrete

  R-set : IsSet R
  R-set = RPower.fixed-power-set

  -- A fibre over the crisp point w of the crisp map const.
  C-discrete : Discrete C
  C-discrete = FiberDiscrete.discrete R-discrete O-discrete const w

  path-is-prop : (q : O (lsuc i)) → IsProp (const q ≡ w)
  path-is-prop q = R-set (const q) w

  C-set : IsSet C
  C-set = Σ-set Lj.O-is-set (λ q → prop-is-set (path-is-prop q))

  inclusion-injective : (c c′ : C) → inclusion c ≡ inclusion c′ → c ≡ c′
  inclusion-injective c c′ = subtype-path path-is-prop

  inclusion-mono : (q : O (lsuc i)) → IsProp (Fiber inclusion q)
  inclusion-mono = injective-fibres inclusion Lj.O-is-set inclusion-injective

  -- The two maps of the comparison. w z is top by computation.
  implication : (q : O (lsuc i)) → const q ≡ w → P → El q
  implication q e z = Lj.truth-out q (happly e z)

  path-from : (q : O (lsuc i)) → (P → El q) → const q ≡ w
  path-from q h = fe-jk (λ z → Lj.truth-in q (h z))

  present : C → Presentation
  present c = inclusion c , implication (inclusion c) (snd c)

  unpresent : Presentation → C
  unpresent t = fst t , path-from (fst t) (snd t)

  implication-is-prop : (q : O (lsuc i)) → IsProp (P → El q)
  implication-is-prop q = pi-is-prop fe-j (λ _ → El-is-prop q)

  present-is-equiv : IsEquiv present
  present-is-equiv =
    quasi-inverse unpresent
      (λ t → subtype-path implication-is-prop refl)
      (λ c → subtype-path path-is-prop refl)

  -- The truth point, in the other presentation, by computation.
  present-truth : present truth-point ≡ (top , λ _ → end-at)
  present-truth = refl
