{-# OPTIONS --safe --without-K --cohesion #-}

-- SUPPLIED small set quotients, as a bounded structure, and what follows
-- from it by itself: induction into propositions, and mere representatives
-- (in QuotientTruncations). Claude (Fable), 14 November 2026; fable-impl-22
-- (HANDOFF-37, item 2; FOUNDATION-CHOICE-M3-AUDIT-01; FABLE-REVIEW-03,
-- section 9.1).
--
-- THIS IS NOT A CONSTRUCTION OF QUOTIENTS. Quotients ℓ is a TYPE of
-- structures. No inhabitant of it is constructed or postulated anywhere in
-- the tree; every module that uses quotients takes the structure as a
-- parameter. Ordinary type theory: no modality is used (--cohesion is in
-- the options because Foundations has it and the flag is infective).
--
-- THE STRUCTURE, AND ITS LEVELS.
--   Quotients ℓ       for every X : Set ℓ and every equivalence relation on
--                     X with values in the propositions of Set ℓ: a
--                     carrier X / R in Set ℓ AGAIN (this is "small"), the
--                     class map, the identification of related points, and
--                     the proof that the carrier is a set. In Set (lsuc ℓ).
--   Eliminates Q w    the universal property of the SAME carriers against
--                     sets of level w: the recursor, its unit law, and the
--                     uniqueness of maps into a set. In Set (lsuc (ℓ ⊔ w)).
-- The property at one level does not give it at another, and a structure
-- with the property at all levels at once would live in Setω and could not
-- stand in a captured telescope (FOUNDATION-CHOICE-M3-AUDIT-01, section 4).
-- So each consumer names the levels it eliminates into, as certificates on
-- one fixed Q. This is the arrangement of the large-target certificates of
-- LargeTarget, for the same reason.
--
-- THE UNIT LAW AND UNIQUENESS ARE POINTWISE. No extensionality principle is
-- part of the structure, and none is used in this module.
--
-- RELATION TO TYPETOPOLOGY. The reference interface is the small
-- set-quotient structure of Quotient/Type.lagda at the project pin
--   52ed2eb58d72a6bab0dd70480fa73e2291b08219,
-- as R37-SMALL-QUOTIENT-REUSE-AUDIT-01, section 1, describes it (its lines
-- 55-69 and 378-394 for the structure, 77-106 for the induction into
-- propositions): a carrier in the join of the universes of the type and of
-- the relation, the unit, the identification of related points, sethood,
-- and unique factorization through the unit into every set of every
-- universe. THAT FILE WAS NOT AMONG THE SOURCES SUPPLIED TO ME. Nothing
-- here is a port of its text; the correspondence is to the audit's
-- description:
--   carrier, unit, related points, sethood   the four fields of Quotients
--   unique factorization                     Eliminates: existence as
--                                            /-rec with /-rec-unit,
--                                            uniqueness as /-unique
-- Two differences. There the relation has its own universe and the
-- property is stated for all target universes at once; here source and
-- relation are at one level and each target level is a certificate. There
-- uniqueness is an identification of factor maps; here it is pointwise.
-- The induction principle below is derived in the way that
-- SMALL-CLOSED-REFLECTION-NATIVE-ROUTE-01, section 4, reports for the
-- reference: by recursion into a Σ-type and uniqueness of maps into the
-- quotient.
module SmallQuotient where

open import Foundations
open import NativeSharp using (transport)
open import SmallPropositions
  using (prop-is-set; subtype-path; retract-is-prop)

------------------------------------------------------------------------
-- 1. A subtype of a set is a set. (TotalBridge.Σ-set is the general
--    statement; it is in a module with --flat-split.)

subtype-set : ∀ {a b} {A : Set a} {B : A → Set b}
            → IsSet A → ((x : A) → IsProp (B x)) → IsSet (Σ A B)
subtype-set {A = A} {B = B} A-set B-prop u w =
  retract-is-prop (ap fst) (subtype-path B-prop) back (A-set (fst u) (fst w))
  where
  back : {w′ : Σ A B} (e : u ≡ w′) → subtype-path B-prop (ap fst e) ≡ e
  back refl = ap (ap (λ t → fst u , t))
    (prop-is-set (B-prop (fst u)) (snd u) (snd u)
       (B-prop (fst u) (snd u) (snd u)) refl)

------------------------------------------------------------------------
-- 2. Equivalence relations with values in the propositions of one level.

record EquivRel {ℓ : Level} (X : Set ℓ) : Set (lsuc ℓ) where
  field
    _≈_ : X → X → Set ℓ
    ≈-prop : (x y : X) → IsProp (x ≈ y)
    ≈-refl : (x : X) → x ≈ x
    ≈-sym : (x y : X) → x ≈ y → y ≈ x
    ≈-trans : (x y z : X) → x ≈ y → y ≈ z → x ≈ z

------------------------------------------------------------------------
-- 3. The supplied structure.

record Quotients (ℓ : Level) : Set (lsuc ℓ) where
  infix 20 _/_
  field
    _/_ : (X : Set ℓ) → EquivRel X → Set ℓ
    [_] : {X : Set ℓ} {R : EquivRel X} → X → X / R
    sound : {X : Set ℓ} {R : EquivRel X} (x y : X)
          → EquivRel._≈_ R x y → [_] {R = R} x ≡ [ y ]
    /-set : {X : Set ℓ} {R : EquivRel X} → IsSet (X / R)

record Eliminates {ℓ : Level} (Q : Quotients ℓ) (w : Level)
       : Set (lsuc (ℓ ⊔ w)) where
  open Quotients Q
  field
    /-rec : {X : Set ℓ} {R : EquivRel X} {Y : Set w} → IsSet Y
          → (f : X → Y) → ((x y : X) → EquivRel._≈_ R x y → f x ≡ f y)
          → X / R → Y
    /-rec-unit : {X : Set ℓ} {R : EquivRel X} {Y : Set w} (Y-set : IsSet Y)
               → (f : X → Y)
               → (resp : (x y : X) → EquivRel._≈_ R x y → f x ≡ f y)
               → (x : X) → /-rec {R = R} Y-set f resp [ x ] ≡ f x
    /-unique : {X : Set ℓ} {R : EquivRel X} {Y : Set w} → IsSet Y
             → (g h : X / R → Y) → ((x : X) → g [ x ] ≡ h [ x ])
             → (z : X / R) → g z ≡ h z

-- EFFECTIVITY, as a type of evidence about a supplied structure: equal
-- classes come from related points. It is not a field of Quotients.
-- QuotientEffectivity derives it from the property at the next level with
-- two extensionality hypotheses; a consumer takes the evidence as a
-- parameter, so it may also be supplied directly (FABLE-REVIEW-03, 9.1 (b)).
Effective : {ℓ : Level} → Quotients ℓ → Set (lsuc ℓ)
Effective {ℓ} Q = {X : Set ℓ} {R : EquivRel X} (x y : X)
                → Quotients.[_] Q {R = R} x ≡ Quotients.[_] Q y
                → EquivRel._≈_ R x y

------------------------------------------------------------------------
-- 4. Induction into propositions of the level of the carrier, from the
--    property at that level. The total space of the family is a set; the
--    recursor gives a map into it; its first component is the identity by
--    uniqueness of maps into the quotient. No extensionality.

module Induction {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ) where

  open Quotients Q
  open Eliminates E

  module _ {X : Set ℓ} {R : EquivRel X} (P : X / R → Set ℓ)
    (P-prop : (z : X / R) → IsProp (P z)) (p : (x : X) → P [ x ]) where

    private
      T-set : IsSet (Σ (X / R) P)
      T-set = subtype-set /-set P-prop

      point : X → Σ (X / R) P
      point x = [ x ] , p x

      point-resp : (x y : X) → EquivRel._≈_ R x y → point x ≡ point y
      point-resp x y r = subtype-path P-prop (sound x y r)

      total : X / R → Σ (X / R) P
      total = /-rec T-set point point-resp

      over : (z : X / R) → fst (total z) ≡ z
      over = /-unique /-set (λ z → fst (total z)) (λ z → z)
        (λ x → ap fst (/-rec-unit T-set point point-resp x))

    /-ind : (z : X / R) → P z
    /-ind z = transport P (over z) (snd (total z))

  -- Two maps into a set of level w that agree on classes agree, restated
  -- with the certificate of the target level as an argument.
  /-unique-into : {w : Level} (E′ : Eliminates Q w)
                → {X : Set ℓ} {R : EquivRel X} {Y : Set w} → IsSet Y
                → (g h : X / R → Y) → ((x : X) → g [ x ] ≡ h [ x ])
                → (z : X / R) → g z ≡ h z
  /-unique-into E′ = Eliminates./-unique E′
