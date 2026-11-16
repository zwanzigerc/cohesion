{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The principal filter: the constructions of HANDOFF-36 put together on
-- ONE schedule of fixed data, ending with the membership equation of the
-- code of the support and with the split closed carrier.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, sections 1
-- to 6; BASE-CLASSIFIER-BOUNDED-MEET-02, sections 1 to 4 and 6;
-- CODISCRETE-POWER-NATIVE-ROUTE-01, section 5).
--
-- Nothing is postulated and nothing is declared. Every datum below is a
-- module parameter. A conditional construction of the library; it is not
-- a theorem of the paper, and no model is claimed for its hypotheses
-- taken together.
--
-- LEVELS. i crisp, j = lsuc i, k = lsuc j.
--
-- THE SCHEDULE. Each module adds parameters to those above it.
--
-- Principal (sX : ShapeData (♯ (O i)))          BEFORE ANY EXTENSIONALITY
--   S₀ = ʃ sX and η₀ = η sX are the carrier and the unit of the support
--   (PrincipalSupport.Carrier), and with them, by definition:
--     e₀, F, u, Q, v, One, point, P           PrincipalSupport.Carrier
--     F-discrete                               from ʃ-discrete sX
--     R, const, w, C, inclusion, truth-point, Presentation
--                                              ClosedCarrier.Carrier at P
--   So the types of all further data are formed from sX alone, before
--   any extensionality hypothesis:
--     ShapeData Q, ShapeData (F → ♯ (O i)), ShapeData (♯ Q), ShapeData R,
--     MonoC F-discrete sX sE.
--
-- Quantified (sQ : ShapeData Q; fe-i, pe-i, fe-j)          sections 1, 2
--   F-set, Q-discrete, Q-set, for-all with its comparisons, P-discrete,
--   P-is-prop, p = for-all u, p-equiv, lower-bound; Decoding (fe-ji) and
--   Truth (pe-j) as in BoundedQuantifier.
--
-- Quantified.Closed (sR : ShapeData R; pe-j, fe-jk)        section 3
--   R-discrete, R-set, C-discrete, C-set, the mono evidence of the
--   inclusion, present-is-equiv.
--
-- Quantified.Closed.Split (tau : Truncation j)             section 4
--   joinP with its decoding, closed-retraction, retracts.
--
-- Quantified.Compared                                      sections 5, 6
--   (sE : ShapeData (F → ♯ (O i)); sY : ShapeData (♯ Q);
--    cQ : LargeOn k sY; sOj : ShapeData (♯ (O j)); pe-j)
--   T-for-all : ʃ sY → ʃ sOj with its unit law       QuantifierShape
--   sigma with its unit law, unit-cong               CodiscretePower
--   eⱼ q = η sOj (sharp-unit q)
--
-- Quantified.Compared.Membership                           section 6
--   (mc : MonoC F-discrete sX sE, ORDINARY, and for that reason last and
--    alone: the maps of Compared do not depend on it)
--   unit-equality : η sY (sharp-unit u) ≡ η sY (sharp-unit v)
--   membership    : eⱼ p ≡ eⱼ top
--
-- THE SHAPE DATA ARE SIX, AND NONE IS MADE FROM ANOTHER.
--   sX   of ♯ (O i)        its carrier is S₀; κ compares into it
--   sQ   of Q = F → O i    proves Q discrete (FixedPower), nothing else
--   sE   of F → ♯ (O i)    the source of the continuity comparison κ
--   sY   of ♯ Q            the source of T-for-all; cQ is ITS certificate
--   sOj  of ♯ (O j)        the target of T-for-all; eⱼ is ITS unit
--   sR   of R = P → O j    proves R discrete (FixedPower), nothing else
-- sQ is not sY and sR is not a shape of ♯ R. The equation unit-equality
-- is about the unit of sY. The certificate cQ is consumed on the carrier
-- and unit of that same sY, and membership is stated with the unit of
-- sOj, so a later consumer that holds sOj has its recursor for the very
-- carrier in which the equation lies.
--
-- HOW membership IS PROVED. A point x of the fibre F stores the path
-- snd x : e₀ (u x) ≡ e₀ top, and e₀ top is e₀ (v x). So u and v have the
-- same unit in S₀ pointwise, and CodiscretePower.unit-cong (the two unit
-- laws of sigma, fe-j for functions F → S₀, and MonoC to cancel sigma)
-- gives unit-equality. Then T-for-all is applied, with its unit law at u
-- and at v, and for-all v ≡ top.
--
-- WHICH PART USES WHAT. MonoC is used by Membership alone. sE, sY, cQ and
-- sOj are used by Compared and Membership alone; these two use no
-- truncation, no fe-jk and no sR. Split takes none of sE, sY, cQ, sOj
-- and mc; the one shape of a ♯-type on which it depends is sX, from which
-- the support P is made. No product axiom, no Nullstellensatz, no
-- stability and no FunExt₂ k k anywhere.
--
-- NAMES. BaseClassifier.C, the type of codes with a proof of discreteness,
-- is hidden here: C is the closed carrier.
module PrincipalFilter where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; MonoC)
open import GlobalPropositions using (FunExt₂; Truncation)
open import SmallPropositions using (PropExt)
open import LargeTarget using (LargeOn)
open import BaseClassifier hiding (C)
import PrincipalSupport
import ClosedCarrier
import JoinRetraction
import QuantifierShape
import CodiscretePower

module Principal {@♭ i : Level} (@♭ sX : ShapeData (♯ (O i))) where

  ----------------------------------------------------------------------
  -- Before any extensionality: the carriers, and the discreteness of F.

  open PrincipalSupport.Discreteness (η sX) (ʃ-discrete sX) public
  open ClosedCarrier.Carrier P public

  ----------------------------------------------------------------------
  -- Sections 1 and 2.

  module Quantified
    (@♭ sQ : ShapeData Q)
    (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
    (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i)) where

    open PrincipalSupport.Facts (η sX) (ʃ-set sX) (ʃ-discrete sX)
           sQ fe-i pe-i fe-j
      public
      hiding (e₀; F; u; Q; v; One; point; P; F-discrete)

    --------------------------------------------------------------------
    -- Section 3, and section 4 in Split.

    module Closed
      (@♭ sR : ShapeData R)
      (@♭ pe-j : PropExt (lsuc i))
      (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i))) where

      open ClosedCarrier.Facts P-discrete sR fe-j pe-j fe-jk public
        hiding (R; const; w; C; inclusion; truth-point; Presentation)

      module Split (@♭ tau : Truncation (lsuc i)) where

        open JoinRetraction.Retraction P-discrete sR fe-j pe-j fe-jk tau
          public
          using (JoinType; join-at; joinP; joinP-β; join-decode;
                 join-encode; join-equiv; left; right; closed-retraction;
                 closed-retraction-inclusion; absorb; retracts;
                 closed-retraction-top)

    --------------------------------------------------------------------
    -- Sections 5 and 6.

    module Compared
      (@♭ sE : ShapeData (F → ♯ (O i)))
      (@♭ sY : ShapeData (♯ Q))
      (@♭ cQ : LargeOn (lsuc (lsuc i)) sY)
      (@♭ sOj : ShapeData (♯ (O (lsuc i))))
      (@♭ pe-j : PropExt (lsuc i)) where

      open Truth pe-j public

      -- The comparison of the three ORIGINAL shapes sX, sE, sY at
      -- A = O i and the support fibre F.
      module Shapes =
        CodiscretePower.Transfer {A = O i} F-discrete fe-j sX sE sY

      -- T (for-all), from the shape sY of ♯ Q to the shape sOj of ♯ (O j).
      module Action =
        QuantifierShape.Naturality F-discrete sQ fe-i pe-i fe-j
          {SQ = ʃ sY} {etaQ = η sY} cQ
          (ʃ sOj) (ʃ-set sOj) (ʃ-discrete sOj) (η sOj)

      open Shapes public
        using (sigma; sigma-unit; sigma-injective; unit-cong;
               unit-A; unit-Q)
      open Action public using (T-for-all; T-for-all-unit)

      -- The coaugmentation O j → T (O j) of sOj.
      eⱼ : O (lsuc i) → ʃ sOj
      eⱼ q = η sOj (sharp-unit q)

      -- The one ordinary hypothesis comes last, in a module of its own:
      -- the maps above do not depend on it and stay crisp terms.
      module Membership (mc : MonoC F-discrete sX sE) where

        -- For the ORIGINAL shape sY of ♯ Q. unit-A is e₀ and v x is top,
        -- by computation; so the path that a point x of the fibre F
        -- stores, snd x : e₀ (u x) ≡ e₀ top, is the pointwise agreement
        -- that unit-cong asks for.
        unit-equality : unit-Q u ≡ unit-Q v
        unit-equality = unit-cong mc u v snd

        -- The code of the support is in the class of top, one level up.
        membership : eⱼ p ≡ eⱼ top
        membership =
          sym (T-for-all-unit u)
          ∙ ap T-for-all unit-equality
          ∙ T-for-all-unit v
          ∙ ap eⱼ for-all-top
