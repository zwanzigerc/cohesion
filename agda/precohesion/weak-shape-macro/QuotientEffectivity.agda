{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Effectivity of a supplied small-quotient structure, derived: equal
-- classes come from related points. Claude (Fable), 14 November 2026;
-- fable-impl-22 (HANDOFF-37, item 3; SMALL-SET-OPEN-CLOSED-GLUING-01,
-- section 1, whose one-row argument this is).
--
-- WHAT IT COSTS. For Q : Quotients ℓ,
--   Eliminates Q (lsuc ℓ)   the property of Q against sets of the NEXT
--                           level, used once, at the set HProp ℓ;
--   FunExt₂ ℓ ℓ, PropExt ℓ  so that logically equivalent propositions of
--                           level ℓ are equal and HProp ℓ is a set
--                           (SmallPropositionLaws, fable-impl-19).
-- All three are ORDINARY arguments. Nothing is postulated. For a quotient
-- kept at level j the one target above j is HProp j, in Set (lsuc j).
--
-- THE ARGUMENT. Fix x. The row t ↦ (x ≈ t) is a map into HProp ℓ that sends
-- related points to equal propositions, by transitivity and symmetry. It
-- descends to the quotient. An identification of the classes of x and y
-- then identifies the propositions x ≈ x and x ≈ y, and reflexivity is
-- carried across. There is no large quotient, no choice of representatives
-- and no function space as a target.
--
-- THE ALTERNATIVE (FABLE-REVIEW-03, section 9.1 (b); asked for by
-- HANDOFF-37, item 3). SmallQuotient.Effective Q is the TYPE of this
-- evidence. A consumer takes e : Effective Q as a parameter and does not
-- ask where it comes from. Supplying e directly, as a further field of the
-- foundation, removes from the premises of that consumer exactly the three
-- items above: the property at lsuc ℓ and the two extensionality
-- hypotheses. The reference derivation (Quotient/Effectivity.lagda of
-- TypeTopology; not ported) goes through an auxiliary large quotient and
-- its truncation infrastructure. It eliminates the small quotient into a
-- carrier of level lsuc ℓ: the SAME level as the one row here. What the
-- one-row proof saves is the auxiliary quotient, not a level.
-- (Corrected in fable-impl-23. The header of fable-impl-22 said that the
-- reference needed the property one level higher; M22-H37-SOURCE-
-- REVIEW-01 compared the source at the pin 52ed2eb5, lines 65 to 72, and
-- found the two targets at the same level. No code is changed.)
--
-- This module has --flat-split only because SmallPropositionLaws has it.
-- It matches on no crisp argument and uses no modality.
module QuotientEffectivity where

open import Foundations
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (HProp; PropExt; hprop-forward)
open import SmallPropositionLaws using (hprop-ext; HProp-is-set)
open import SmallQuotient

module OneRow {ℓ : Level} (Q : Quotients ℓ) (E⁺ : Eliminates Q (lsuc ℓ))
  (fe : FunExt₂ ℓ ℓ) (pe : PropExt ℓ) where

  open Quotients Q
  open Eliminates E⁺

  module _ {X : Set ℓ} {R : EquivRel X} (x : X) where

    open EquivRel R

    row : X → HProp ℓ
    row t = (x ≈ t) , ≈-prop x t

    row-respects : (t t′ : X) → t ≈ t′ → row t ≡ row t′
    row-respects t t′ r = hprop-ext fe pe
      (λ a → ≈-trans x t t′ a r)
      (λ a → ≈-trans x t′ t a (≈-sym t t′ r))

    code : X / R → HProp ℓ
    code = /-rec (HProp-is-set fe pe) row row-respects

    code-unit : (t : X) → code [ t ] ≡ row t
    code-unit = /-rec-unit (HProp-is-set fe pe) row row-respects

  effective : Effective Q
  effective {X} {R} x y e =
    hprop-forward (sym (code-unit x x) ∙ ap (code x) e ∙ code-unit x y)
      (EquivRel.≈-refl R x)
