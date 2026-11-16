{-# OPTIONS --safe --without-K --cohesion #-}

-- The two small truncations FROM a supplied small-quotient structure:
--   propositional truncation   the quotient by the total relation
--   set truncation             the quotient by "merely equal"
-- with their recursors, unit laws and uniqueness, at the level of the
-- structure and at every further level for which the structure has its
-- universal property. Claude (Fable), 14 November 2026; fable-impl-22
-- (HANDOFF-37, item 2; FOUNDATION-CHOICE-M3-AUDIT-01, section 3;
-- SMALL-CLOSED-REFLECTION-NATIVE-ROUTE-01, section 4).
--
-- Literally --safe. Ordinary type theory; no modality. NOTHING IS
-- CONSTRUCTED FROM NOTHING: every definition is under a parameter
-- Q : Quotients ℓ with E : Eliminates Q ℓ. The carriers are quotients of Q
-- and stay in Set ℓ.
--
-- NO EXTENSIONALITY IS USED, of functions or of propositions. In
-- particular the quotient by the total relation is shown to be a
-- proposition by two inductions with one endpoint held fixed
-- (SMALL-CLOSED-REFLECTION-NATIVE-ROUTE-01, section 4), not by the
-- function-valued motive of the reference proof. This is possible because
-- the uniqueness field of Eliminates is pointwise.
--
-- LEVELS. With E : Eliminates Q ℓ the recursors go into propositions and
-- sets of level ℓ. With a further certificate E′ : Eliminates Q w they go
-- into level w, ON THE SAME CARRIERS: prop-rec-into, set-rec-into. For the
-- set truncation the truncation that defines "merely equal" must itself
-- eliminate into level w; the derived one does, by the same E′.
--
-- REFERENCE. Quotient/GivesPropTrunc.lagda of TypeTopology at the project
-- pin 52ed2eb58d72a6bab0dd70480fa73e2291b08219, as described by
-- FOUNDATION-CHOICE-M3-AUDIT-01 (section 1, its lines 22-60) and
-- R37-SMALL-QUOTIENT-REUSE-AUDIT-01 (section 1), is the construction of the
-- first truncation; that file was not among the sources supplied to me and
-- no text of it is ported. The second construction is the one proposed in
-- FOUNDATION-CHOICE-M3-AUDIT-01, section 3, which says that no
-- implementation of it was located.
module QuotientTruncations where

open import Foundations
open import SmallPropositions using (prop-is-set)
open import OrdinaryTruncation
open import SmallQuotient

-- A one-point type at any level, for the total relation.
record One (ℓ : Level) : Set ℓ where
  constructor one

------------------------------------------------------------------------
-- 1. Propositional truncation.

module PropFromQuotients {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  where

  open Quotients Q
  open Induction Q E

  total-relation : (X : Set ℓ) → EquivRel X
  total-relation X = record
    { _≈_ = λ _ _ → One ℓ
    ; ≈-prop = λ _ _ _ _ → refl
    ; ≈-refl = λ _ → one
    ; ≈-sym = λ _ _ _ → one
    ; ≈-trans = λ _ _ _ _ _ → one
    }

  Trunc : Set ℓ → Set ℓ
  Trunc X = X / total-relation X

  unit : {X : Set ℓ} → X → Trunc X
  unit = [_]

  -- First the class of x is identified with every point; then every point
  -- with every point. Both motives are identity types in the set Trunc X.
  private
    to-class : {X : Set ℓ} (x : X) (v : Trunc X) → unit x ≡ v
    to-class {X} x = /-ind (λ v → unit x ≡ v) (λ v → /-set (unit x) v)
      (λ y → sound x y one)

  trunc-is-prop : {X : Set ℓ} → IsProp (Trunc X)
  trunc-is-prop {X} u v =
    /-ind (λ u′ → u′ ≡ v) (λ u′ → /-set u′ v) (λ x → to-class x v) u

  -- The recursor into propositions of any level at which Q eliminates.
  rec-into : {w : Level} (E′ : Eliminates Q w) {X : Set ℓ} {P : Set w}
           → IsProp P → (X → P) → Trunc X → P
  rec-into E′ P-prop f =
    Eliminates./-rec E′ (prop-is-set P-prop) f (λ x y _ → P-prop (f x) (f y))

  prop-truncation : PropTruncation ℓ
  prop-truncation = record
    { ∥_∥ = Trunc
    ; ∣_∣ = unit
    ; squash = trunc-is-prop
    ; ∥-rec = rec-into E
    }

  prop-rec-into : {w : Level} → Eliminates Q w
                → PropRecInto prop-truncation w
  prop-rec-into E′ = rec-into E′

------------------------------------------------------------------------
-- 2. Set truncation, for ANY supplied propositional truncation T of the
--    same level. "Merely equal" is an equivalence relation by three uses
--    of the recursor of T at its own level.

module SetFromQuotients {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) where

  open Quotients Q
  open PropTruncation T

  merely-equal : (X : Set ℓ) → EquivRel X
  merely-equal X = record
    { _≈_ = λ x y → ∥ x ≡ y ∥
    ; ≈-prop = λ _ _ → squash
    ; ≈-refl = λ _ → ∣ refl ∣
    ; ≈-sym = λ _ _ → ∥-map sym
    ; ≈-trans = λ _ _ _ r r′ →
        ∥-rec squash (λ e → ∥-map (λ e′ → e ∙ e′) r′) r
    }

  SetTrunc : Set ℓ → Set ℓ
  SetTrunc X = X / merely-equal X

  set-unit : {X : Set ℓ} → X → SetTrunc X
  set-unit = [_]

  -- Against sets of level w: E′ is the property of Q at w, and `into`
  -- eliminates T into the propositions of level w, here f x ≡ f y.
  module Into {w : Level} (E′ : Eliminates Q w) (into : PropRecInto T w)
    where

    private
      respects : {X : Set ℓ} {D : Set w} (D-set : IsSet D) (f : X → D)
               → (x y : X) → ∥ x ≡ y ∥ → f x ≡ f y
      respects D-set f x y = into (D-set (f x) (f y)) (ap f)

    set-rec : {X : Set ℓ} {D : Set w} → IsSet D → (X → D) → SetTrunc X → D
    set-rec D-set f = Eliminates./-rec E′ D-set f (respects D-set f)

    set-rec-unit : {X : Set ℓ} {D : Set w} (D-set : IsSet D) (f : X → D)
                 → (x : X) → set-rec D-set f (set-unit x) ≡ f x
    set-rec-unit D-set f =
      Eliminates./-rec-unit E′ D-set f (respects D-set f)

    set-unique : {X : Set ℓ} {D : Set w} → IsSet D → (g h : SetTrunc X → D)
               → ((x : X) → g (set-unit x) ≡ h (set-unit x))
               → (z : SetTrunc X) → g z ≡ h z
    set-unique = Eliminates./-unique E′

  private
    module Own = Into E (own-level T)

  set-truncation : SetTruncation ℓ
  set-truncation = record
    { τ₀ = SetTrunc
    ; ∣_∣₀ = set-unit
    ; τ₀-set = /-set
    ; τ₀-rec = Own.set-rec
    ; τ₀-rec-unit = Own.set-rec-unit
    ; τ₀-unique = Own.set-unique
    }

  set-rec-into : {w : Level} → Eliminates Q w → PropRecInto T w
               → SetRecInto set-truncation w
  set-rec-into E′ into = record
    { rec-into = I.set-rec
    ; rec-into-unit = I.set-rec-unit
    ; unique-into = I.set-unique
    }
    where module I = Into E′ into

------------------------------------------------------------------------
-- 3. Both from the quotient structure alone: the set truncation whose
--    "merely" is the truncation of part 1.

module FromQuotients {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ) where

  open PropFromQuotients Q E public
    using (prop-truncation; prop-rec-into; trunc-is-prop)

  open SetFromQuotients Q E prop-truncation public
    using (set-truncation; merely-equal)

  set-truncation-into : {w : Level} → Eliminates Q w
                      → SetRecInto set-truncation w
  set-truncation-into E′ =
    SetFromQuotients.set-rec-into Q E prop-truncation E′ (prop-rec-into E′)

------------------------------------------------------------------------
-- 4. Every point of a quotient merely has a representative. The
--    truncation is any supplied one of the level; the fibre is in Set ℓ.

module Representatives {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) where

  open Quotients Q
  open Induction Q E
  open PropTruncation T

  representative : {X : Set ℓ} {R : EquivRel X} (z : X / R)
                 → ∥ Fiber ([_] {R = R}) z ∥
  representative = /-ind (λ z → ∥ Fiber [_] z ∥) (λ _ → squash)
    (λ x → ∣ x , refl ∣)
