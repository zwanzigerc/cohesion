{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The principal filter in use: one client that holds all the fixed data of
-- HANDOFF-36 at once and reads off the mixed-level unit law, the
-- membership equation and the split closed carrier.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, the
-- principal client of sections 5 and 6, and of the whole schedule).
--
-- SUPPLIED DATA. Nothing is declared or postulated in this file or in a
-- PROJECT module of its import closure, and none of them runs a reflection
-- program that declares anything. (The compiler's builtin modules are in
-- that closure too and have the compiler's own builtin axioms.)
-- Hypotheses, all module parameters. Crisp:
--   sX  : ShapeData (♯ (O i))             the shape whose carrier is S₀
--   sQ  : ShapeData Q                     for the discreteness of Q
--   sE  : ShapeData (F → ♯ (O i))         for the continuity comparison
--   sY  : ShapeData (♯ Q)                 the shape of ♯ Q
--   cQ  : LargeOn (lsuc (lsuc i)) sY      its larger-target certificate
--   sOj : ShapeData (♯ (O (lsuc i)))      the shape of ♯ (O j)
--   sR  : ShapeData R                     for the discreteness of R
--   tau : Truncation (lsuc i)             a small truncation structure
--   fe-i, pe-i, fe-j, pe-j, fe-jk
-- Ordinary, each in a module of its own:
--   fe-ji : FunExt₂ (lsuc i) i            section 2 of this file
--   mc    : MonoC F-discrete sX sE        section 4 of this file
-- Section 6 takes these two CRISPLY, as parameters of its own module, and
-- puts a result of each in a box: a later crisp use supplies the
-- hypothesis crisply at the call.
-- The types of sQ, sE, sY, sR and mc mention the carriers F, Q, P, R of
-- the support; these are written with PrincipalSupport.Carrier and
-- ClosedCarrier.Carrier at (ʃ sX, η sX), which take no hypothesis.
--
-- No instance of these hypotheses is constructed here, and that they can
-- hold together in a model is not claimed by this file.
module PrincipalFilterExamples where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-discrete; η; rec; MonoC)
open import GlobalPropositions using (FunExt₂; Truncation)
open import SmallPropositions using (PropExt)
open import LargeTarget using (LargeOn)
open import BaseClassifier hiding (C)
import PrincipalSupport
import ClosedCarrier
open import PrincipalFilter

-- The carriers of the support of a shape of ♯ (O i): no hypothesis.
module Carriers {@♭ i : Level} (@♭ sX : ShapeData (♯ (O i))) where
  open PrincipalSupport.Carrier (ʃ sX) (η sX) public
  open ClosedCarrier.Carrier P public

module Client {@♭ i : Level}
  (@♭ sX : ShapeData (♯ (O i)))
  (@♭ sQ : ShapeData (Carriers.Q sX))
  (@♭ sE : ShapeData (Carriers.F sX → ♯ (O i)))
  (@♭ sY : ShapeData (♯ (Carriers.Q sX)))
  (@♭ cQ : LargeOn (lsuc (lsuc i)) sY)
  (@♭ sOj : ShapeData (♯ (O (lsuc i))))
  (@♭ sR : ShapeData (Carriers.R sX))
  (@♭ tau : Truncation (lsuc i))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) (@♭ pe-j : PropExt (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i))) where

  module Before = Carriers sX

  open Principal sX
  open Quantified sQ fe-i pe-i fe-j
  open Closed sR pe-j fe-jk
  open Split tau
  open Compared sE sY cQ sOj pe-j

  ----------------------------------------------------------------------
  -- 1. The carriers at the end of the schedule are those that were
  --    formed before any hypothesis. All by computation.

  same-fibre : F ≡ Before.F
  same-fibre = refl

  same-power : Q ≡ Before.Q
  same-power = refl

  same-support : P ≡ Before.P
  same-support = refl

  same-second-power : R ≡ Before.R
  same-second-power = refl

  same-closed-carrier : C ≡ Before.C
  same-closed-carrier = refl

  -- The carrier and the unit of the support are those of sX.
  support-unit : (q : O i) → e₀ q ≡ η sX (sharp-unit q)
  support-unit q = refl

  ----------------------------------------------------------------------
  -- 2. The quantifier and the code of the support.

  code-of-support : O (lsuc i)
  code-of-support = p

  code-is : p ≡ for-all u
  code-is = refl

  module Decoded (fe-ji : FunExt₂ (lsuc i) i) where
    open Decoding fe-ji

    everywhere : (g : Q) → IsEquiv (decode-all g)
    everywhere = decode-all-equiv

  ----------------------------------------------------------------------
  -- 3. The mixed-level unit law. Its source is the carrier of sY, of
  --    Set (lsuc i); its target is the carrier of sOj, one universe up.

  action : ʃ sY → ʃ sOj
  action = T-for-all

  unit-law : (g : Q)
           → T-for-all (η sY (sharp-unit g))
             ≡ η sOj (sharp-unit (for-all g))
  unit-law = T-for-all-unit

  -- The later consumer keeps the recursor of sOj for that same carrier:
  -- a map out of ʃ sOj into a discrete set of its level is still to be
  -- had, and its source is the type in which eⱼ p and eⱼ top lie.
  later-recursor :
    (@♭ D : Set (lsuc (lsuc i))) (@♭ D-set : IsSet D)
    (@♭ D-discrete : Discrete D)
    → (@♭ f : ♯ (O (lsuc i)) → D) → ʃ sOj → D
  later-recursor = rec sOj

  ----------------------------------------------------------------------
  -- 4. The membership equation, and what depends on MonoC.

  module WithMonoC (mc : MonoC F-discrete sX sE) where
    open Membership mc

    -- On the unit of the ORIGINAL shape sY of ♯ Q.
    units-agree : η sY (sharp-unit u) ≡ η sY (sharp-unit v)
    units-agree = unit-equality

    -- On the unit of sOj: the code of the support is in the class of top.
    in-top-class : η sOj (sharp-unit p) ≡ η sOj (sharp-unit top)
    in-top-class = membership

  ----------------------------------------------------------------------
  -- 5. The closed carrier, with the code of the support as a point.

  -- Under P the code p holds; so p is a code of the closed carrier.
  bottom-point : C
  bottom-point = unpresent (p , P-to-p)

  bottom-code : inclusion bottom-point ≡ p
  bottom-code = refl

  -- The retraction sends the code of the support to that point, and the
  -- top code to the truth point.
  onto-bottom : closed-retraction p ≡ bottom-point
  onto-bottom = retracts bottom-point

  onto-truth : closed-retraction top ≡ truth-point
  onto-truth = closed-retraction-top

  -- So the join with the support fixes p.
  join-fixes-support : joinP p ≡ p
  join-fixes-support = absorb bottom-point

  -- The split law at every point.
  split : (c : C) → closed-retraction (inclusion c) ≡ c
  split = retracts

  ----------------------------------------------------------------------
  -- 6. A later CRISP use. fe-ji and mc are ordinary parameters of
  --    Decoding and of Membership, and inside those two modules their
  --    results are not crisp terms. A client that needs such a result
  --    crisply takes the hypothesis as a crisp parameter of ITS module and
  --    applies the library module to it: then every variable of the
  --    result is crisp. Here each result is put in a box, which accepts
  --    crisp terms only.

  module CrispLater
    (@♭ fe-ji : FunExt₂ (lsuc i) i)
    (@♭ mc : MonoC F-discrete sX sE) where

    open Decoding fe-ji
    open Membership mc

    boxed-membership : ♭ (η sOj (sharp-unit p) ≡ η sOj (sharp-unit top))
    boxed-membership = box membership

    boxed-decoding : ♭ (IsEquiv (decode-all u))
    boxed-decoding = box (decode-all-equiv u)
