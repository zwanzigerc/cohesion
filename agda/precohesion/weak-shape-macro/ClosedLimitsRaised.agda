{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE CLOSED REFLECTOR AT A HIGHER SUPPORT: the i-small pullback, raised.
-- Opus, 14 November 2026; opus-closed-limits-01, implementing
-- OPUS-CLOSED-LIMITS-AND-DETECTION-RELEASE-01.txt, item 3.
--
-- Only the levels i, b are crisp (Raise asks for it). The quotient
-- structure Q, elimination E, truncation T at level i ⊔ b, the support
-- P : Set (i ⊔ b), its propositionality and the evidence
-- effective : Effective Q are ORDINARY; no discreteness of P is needed
-- (as in SetSourceReflectionStatements.AtLevel; OPUS-SET-SOURCE-R-RELEASE-02).
-- cP W = c (Raise b W), unitP, pointP are, by definition, those of
-- ClosedReflectionRaised.AtSupport; the raised action on a map is
-- c-map (raised f) with raised f r = raise (f (lower r)). The reflection is
-- instantiated ONCE, at the level written i ⊔ b (FABLE-PLAN-SET-SOURCE-
-- TRANCHE-R-01 section 5.1: two instantiations at differently written
-- levels made conversion stall). With b = lsuc i this is j = i + 1.
--
-- For i-small X, Y, Z (Z a set) and f : X → Z, g : Y → Z:
--   to / from, to-equiv     an EXPLICIT equivalence
--                           Raise b (Pullback f g) ≃ Pullback (raised f) (raised g)
--                           (no assumption that these types convert), with its
--                           projected paths to-projY, to-projX (refl on raise);
--   c-to-equiv              c carries it to an equivalence (c-map-compose,
--                           ClosedLimits.c-map-cong, c-map-id);
--   κP, κP-equiv            the raised canonical comparison
--                           cP (Pullback f g) → Pullback (c-map (raised f)) (c-map (raised g)),
--                           an equivalence;
--   κP-projY, κP-projX      its projections are c-map of the raised projections;
--   κP-unitP, κP-pointP     its generator laws at unitP and pointP.
-- RaisedDetection: joint detection for an i-small h between sets, from
-- P → IsEquiv h and IsEquiv (c-map (raised h)), by detection at the raised
-- map and the raise/lower transfer of equivalences.
--
-- Nothing is postulated; no shape, continuity, Nullstellensatz, choice or
-- extensionality. Not --safe (imports with --flat-split).
module ClosedLimitsRaised where

open import Foundations
open import Adjointify using (quasi-inverse)
open import CaptureContext using (Raise; raise; lower; raise-lower)
open import PullbackSetFibers using (Pullback; retract-set)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import ClosedReflection using (module Reflection)
open import ClosedLimits
  using (module Limits; pb-path; equiv-compose)

-- The raise of a set is a set (as ShapeElim.raise-set, without importing
-- the frontend).
raise-set : {@♭ a b : Level} {A : Set a} → IsSet A → IsSet (Raise b A)
raise-set = retract-set lower raise raise-lower

module AtSupportLimits {@♭ i b : Level} (Q : Quotients (i ⊔ b))
  (E : Eliminates Q (i ⊔ b)) (T : PropTruncation (i ⊔ b))
  (P : Set (i ⊔ b)) (P-prop : IsProp P) (effective : Effective Q) where

  open Reflection Q E T P P-prop
  open Limits Q E T P P-prop effective

  -- By definition those of ClosedReflectionRaised.AtSupport.
  cP : Set i → Set (i ⊔ b)
  cP W = c (Raise b W)

  unitP : {W : Set i} → W → cP W
  unitP w = inX (raise w)

  pointP : {W : Set i} → P → cP W
  pointP = inP

  -- The raised action on maps.
  raised : {X Y : Set i} → (X → Y) → Raise b X → Raise b Y
  raised f r = raise (f (lower r))

  cP-map : {X Y : Set i} → (X → Y) → cP X → cP Y
  cP-map f = c-map (raised f)

  cP-map-unitP : {X Y : Set i} (f : X → Y) (x : X)
               → cP-map f (unitP x) ≡ unitP (f x)
  cP-map-unitP f x = c-map-inX (raised f) (raise x)

  cP-map-pointP : {X Y : Set i} (f : X → Y) (p : P)
                → cP-map f (pointP p) ≡ pointP p
  cP-map-pointP f = c-map-inP (raised f)

  ----------------------------------------------------------------------
  -- The raised pullback.

  module Raised {X Y Z : Set i} (Z-set : IsSet Z) (f : X → Z) (g : Y → Z)
    where

    Zᵣ-set : IsSet (Raise b Z)
    Zᵣ-set = raise-set Z-set

    module K = Comparison Zᵣ-set (raised f) (raised g)

    to : Raise b (Pullback f g) → Pullback (raised f) (raised g)
    to (raise (y , x , e)) = raise y , raise x , ap raise e

    from : Pullback (raised f) (raised g) → Raise b (Pullback f g)
    from (ry , rx , e) = raise (lower ry , lower rx , ap lower e)

    from-to : (w : Raise b (Pullback f g)) → from (to w) ≡ w
    from-to (raise (y , x , e)) = ap raise (pb-path Z-set refl refl)

    to-from : (v : Pullback (raised f) (raised g)) → to (from v) ≡ v
    to-from (raise y , raise x , e) = pb-path Zᵣ-set refl refl

    to-equiv : IsEquiv to
    to-equiv = quasi-inverse from to-from from-to

    -- The projected paths of the explicit equivalence.
    to-projY : (w : Raise b (Pullback f g)) → fst (to w) ≡ raise (fst (lower w))
    to-projY (raise _) = refl

    to-projX : (w : Raise b (Pullback f g))
             → fst (snd (to w)) ≡ raise (fst (snd (lower w)))
    to-projX (raise _) = refl

    -- c carries the explicit equivalence to an equivalence.
    c-to : cP (Pullback f g) → c (Pullback (raised f) (raised g))
    c-to = c-map to

    c-to-equiv : IsEquiv c-to
    c-to-equiv = quasi-inverse (c-map from)
      (λ z → sym (c-map-compose to from z)
             ∙ c-map-cong (λ v → to (from v)) (λ v → v) to-from z
             ∙ c-map-id z)
      (λ z → sym (c-map-compose from to z)
             ∙ c-map-cong (λ w → from (to w)) (λ w → w) from-to z
             ∙ c-map-id z)

    -- The raised canonical comparison.
    κP : cP (Pullback f g) → K.H
    κP z = K.κ (c-to z)

    κP-equiv : IsEquiv κP
    κP-equiv = equiv-compose c-to-equiv K.κ-equiv

    -- Its projections are c-map of the raised projections.
    κP-projY : (z : cP (Pullback f g))
             → fst (κP z) ≡ cP-map (λ (d : Pullback f g) → fst d) z
    κP-projY z = sym (c-map-compose K.projY to z)
      ∙ c-map-cong (λ w → K.projY (to w)) (λ w → raise (fst (lower w)))
          to-projY z

    κP-projX : (z : cP (Pullback f g))
             → fst (snd (κP z)) ≡ cP-map (λ (d : Pullback f g) → fst (snd d)) z
    κP-projX z = sym (c-map-compose K.projX to z)
      ∙ c-map-cong (λ w → K.projX (to w)) (λ w → raise (fst (snd (lower w))))
          to-projX z

    -- The generator laws at unitP and pointP.
    κP-unitP : (d : Pullback f g) → κP (unitP d) ≡ K.inX-point (to (raise d))
    κP-unitP d = ap K.κ (c-map-inX to (raise d)) ∙ K.κ-inX (to (raise d))

    κP-pointP : (p : P) → κP (pointP p) ≡ K.inP-point p
    κP-pointP p = ap K.κ (c-map-inP to p) ∙ K.κ-inP p

  ----------------------------------------------------------------------
  -- Joint detection for i-small maps.

  module RaisedDetection {X Y : Set i} (X-set : IsSet X) (Y-set : IsSet Y)
    (h : X → Y) where

    raise-equiv : IsEquiv h → IsEquiv (raised h)
    raise-equiv e = quasi-inverse (λ r → raise (inverse e (lower r)))
      (λ r → ap raise (section e (lower r)) ∙ raise-lower r)
      (λ r → ap raise (retraction e (lower r)) ∙ raise-lower r)

    lower-equiv : IsEquiv (raised h) → IsEquiv h
    lower-equiv e = quasi-inverse (λ y → lower (inverse e (raise y)))
      (λ y → ap lower (section e (raise y)))
      (λ x → ap lower (retraction e (raise x)))

    private
      module D = Detection (raise-set X-set) (raise-set Y-set) (raised h)

    detectP : (P → IsEquiv h) → IsEquiv (cP-map h) → IsEquiv h
    detectP open-equiv closed-equiv =
      lower-equiv (D.detect (λ p → raise-equiv (open-equiv p)) closed-equiv)
