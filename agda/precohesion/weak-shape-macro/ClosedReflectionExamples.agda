{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Clients of the closed reflection at the two levels of the handoff: a
-- type W in Set i and a support P in Set j, j = i + 1. Claude (Fable),
-- 14 November 2026; fable-impl-22 (HANDOFF-37, item 3).
--
-- Nothing is postulated. The quotient structure at j, its property at j,
-- the support with its proofs are crisp PARAMETERS; the truncation is the
-- one derived from the quotient structure, so that the whole construction
-- comes from that one supplied structure. The hypotheses of effectivity
-- (the property at j + 1 and two extensionality principles at j) are
-- ORDINARY and are the parameters of the last module only: the carrier,
-- its closedness, its discreteness and its universal properties are
-- formed before them.
module ClosedReflectionExamples where

open import Foundations
open import GlobalPropositions using (FunExt₂)
open import DecidableData using (⊥)
open import SmallPropositions using (PropExt)
open import TruncationDiscrete using (_⊎_)
open import OrdinaryTruncation
open import SmallQuotient
open import QuotientTruncations using (module FromQuotients)
open import QuotientEffectivity using (module OneRow)
open import ClosedReflection using (Closed)
open import ClosedReflectionRaised

module AtNextLevel {@♭ i : Level} (@♭ Q : Quotients (lsuc i))
  (@♭ E : Eliminates Q (lsuc i))
  (@♭ P : Set (lsuc i)) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P) where

  T : PropTruncation (lsuc i)
  T = FromQuotients.prop-truncation Q E

  open PropTruncation T
  open AtSupport {i = i} {b = lsuc i} Q E T P P-prop dP

  -- The reflection of a type of level i is kept at level j = lsuc i.
  carrier : Set i → Set (lsuc i)
  carrier = cP

  closed-carrier : {W : Set i} → Closed P (cP W)
  closed-carrier = cP-closed

  discrete-carrier : {@♭ W : Set i} (@♭ dW : Discrete W) → Discrete (cP W)
  discrete-carrier = cP-discrete

  -- The two-generator property into a set D of level j that need NOT be
  -- closed (SET-MAIN-FIXED-DATA-AND-STAGING-01 uses it at discrete D).
  into-a-set : {W : Set i} {D : Set (lsuc i)} → IsSet D
             → (f : W → D) (g : P → D) → ((x : W) (p : P) → f x ≡ g p)
             → cP W → D
  into-a-set D-set f g h = CoconeP.extendP E (own-level T) D-set f g h

  into-a-set-unit : {W : Set i} {D : Set (lsuc i)} (D-set : IsSet D)
                  → (f : W → D) (g : P → D)
                  → (h : (x : W) (p : P) → f x ≡ g p)
                  → (x : W) → into-a-set D-set f g h (unitP x) ≡ f x
  into-a-set-unit D-set f g h =
    CoconeP.extendP-unit E (own-level T) D-set f g h

  -- A type without points still has the generator of the support.
  empty-case : {W : Set i} → (W → ⊥) → IsEquiv (pointP {W})
  empty-case = Empty.point-equiv

  -- Equal units come from equal points or from the support. The three
  -- hypotheses are ordinary, and they are the last parameters.
  module WithEffectivity (E⁺ : Eliminates Q (lsuc (lsuc i)))
    (fe : FunExt₂ (lsuc i) (lsuc i)) (pe : PropExt (lsuc i)) where

    effective : Effective Q
    effective = OneRow.effective Q E⁺ fe pe

    unit-test : {W : Set i} (x x′ : W) → unitP x ≡ unitP x′
              → ∥ (x ≡ x′) ⊎ P ∥
    unit-test = TestP.unitP-test effective

-- The same at the concrete levels zero and one.
module AtZero (@♭ Q : Quotients (lsuc lzero))
  (@♭ E : Eliminates Q (lsuc lzero))
  (@♭ P : Set₁) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P) where

  open AtNextLevel {i = lzero} Q E P P-prop dP

  carrier₀ : Set → Set₁
  carrier₀ = carrier

  discrete₀ : {@♭ W : Set} (@♭ dW : Discrete W) → Discrete (carrier₀ W)
  discrete₀ = discrete-carrier
