{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The closed reflection of a type of a LOWER level at a support of a higher
-- one:  c_P W = (Raise W ⊎ P) / R,  R s t = ∥ (s ≡ t) ⊎ P ∥.
-- Claude (Fable), 14 November 2026; fable-impl-22 (HANDOFF-37, item 3).
--
-- W is in Set i and the support P in Set (i ⊔ b); with b = lsuc i this is
-- the case of the handoff, P in Set j for j = i + 1, and c_P W in Set j
-- again. W is raised by the existing CaptureContext.Raise, so that its
-- discreteness is the existing ShapeElim.raise-discrete. Everything else is
-- ClosedReflection at the raised type; this module only restates what a
-- client at the two levels needs, with the raise and lower in place.
--
-- Nothing is postulated. The quotient structure, its property at its own
-- level, the truncation, the support, its proof of being a proposition and
-- its discreteness are crisp parameters; the last is used only by
-- cP-discrete.
--
-- EMPTY W. If W has no point, the P-generator P → c_P W is an equivalence:
-- the sum has the second summand, and the reflection of the empty type is
-- P, not the empty type (module Empty).
module ClosedReflectionRaised where

open import Foundations
open import Adjointify using (quasi-inverse)
open import CaptureContext using (Raise; raise; lower)
open import ShapeElim using (raise-discrete)
open import DecidableData using (⊥)
open import SmallPropositions using (prop-is-set)
open import TruncationDiscrete using (_⊎_; inl; inr)
open import OrdinaryTruncation
open import SmallQuotient
open import ClosedReflection

module AtSupport {@♭ i b : Level} (@♭ Q : Quotients (i ⊔ b))
  (@♭ E : Eliminates Q (i ⊔ b)) (@♭ T : PropTruncation (i ⊔ b))
  (@♭ P : Set (i ⊔ b)) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P) where

  open PropTruncation T
  open Reflection Q E T P P-prop

  cP : Set i → Set (i ⊔ b)
  cP W = c (Raise b W)

  unitP : {W : Set i} → W → cP W
  unitP w = inX (raise w)

  pointP : {W : Set i} → P → cP W
  pointP = inP

  glueP : {W : Set i} (w : W) (p : P) → unitP w ≡ pointP p
  glueP w p = glue (raise w) p

  cP-set : {W : Set i} → IsSet (cP W)
  cP-set = c-set

  cP-closed : {W : Set i} → Closed P (cP W)
  cP-closed = closed

  -- The lower-level type is discrete; so is its reflection.
  cP-discrete : {@♭ W : Set i} (@♭ dW : Discrete W) → Discrete (cP W)
  cP-discrete dW =
    Discreteness.discrete Q E T P P-prop dP (raise-discrete dW)

  -- The two-generator property with the maps given on W itself.
  module CoconeP {W : Set i} {w : Level} (E′ : Eliminates Q w)
    (into : PropRecInto T w) {Y : Set w} (Y-set : IsSet Y)
    (f : W → Y) (g : P → Y) (h : (x : W) (p : P) → f x ≡ g p) where

    private
      module C = Cocone {X = Raise b W} E′ into Y-set
        (λ r → f (lower r)) g (λ r p → h (lower r) p)

    extendP : cP W → Y
    extendP = C.extend

    extendP-unit : (x : W) → extendP (unitP x) ≡ f x
    extendP-unit x = C.extend-inX (raise x)

    extendP-point : (p : P) → extendP (pointP p) ≡ g p
    extendP-point = C.extend-inP

  generatorsP-unique : {W : Set i} {w : Level} (E′ : Eliminates Q w)
                     → {Y : Set w} → IsSet Y → (u v : cP W → Y)
                     → ((x : W) → u (unitP x) ≡ v (unitP x))
                     → ((p : P) → u (pointP p) ≡ v (pointP p))
                     → (z : cP W) → u z ≡ v z
  generatorsP-unique E′ Y-set u v on-W =
    generators-unique E′ Y-set u v on-raised
    where
    on-raised : (r : Raise b _) → u (inX r) ≡ v (inX r)
    on-raised (raise x) = on-W x

  -- The reflection of the empty type is the support.
  module Empty {W : Set i} (no-point : W → ⊥) where

    private
      absurd : ∀ {a} {A : Set a} → ⊥ → A
      absurd ()

      module B = CoconeP E (own-level T) (prop-is-set P-prop)
        (λ x → absurd (no-point x)) (λ p → p)
        (λ x p → absurd (no-point x))

    to-support : cP W → P
    to-support = B.extendP

    point-equiv : IsEquiv (pointP {W})
    point-equiv = quasi-inverse to-support
      (generatorsP-unique E cP-set (λ z → pointP (to-support z)) (λ z → z)
        (λ x → absurd (no-point x))
        (λ p → ap pointP (B.extendP-point p)))
      B.extendP-point

  -- Equal units come from equal points or from the support, given
  -- evidence of effectivity.
  module TestP (effective : Effective Q) {W : Set i} where

    private
      lowered : {x x′ : W} → (raise {b = b} x ≡ raise x′) ⊎ P
              → (x ≡ x′) ⊎ P
      lowered (inl e) = inl (ap lower e)
      lowered (inr p) = inr p

    -- (x ≡ x′) is in Set i and P in Set (i ⊔ b): the sum is at the level
    -- of the truncation.
    unitP-test : (x x′ : W) → unitP x ≡ unitP x′ → ∥ (x ≡ x′) ⊎ P ∥
    unitP-test x x′ e =
      ∥-map lowered (Test.inX-test effective (raise x) (raise x′) e)
