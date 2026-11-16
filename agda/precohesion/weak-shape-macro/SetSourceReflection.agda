{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE TRANCHE R, statements R1–R3 and R1P–R3P: proofs.
-- Opus, 14 November 2026; opus-closed-limits-01 (delta 02), implementing
-- OPUS-SET-SOURCE-R-RELEASE-02.txt and FABLE-PLAN-SET-SOURCE-TRANCHE-R-01
-- sections 2–4, against Fable's UNCHANGED SetSourceReflectionStatements.
--
-- The statements are Fable's types (Gluing, Gluing.Pullback, AtLevel,
-- AtLevel.PullbackP); the maps κ and κP are Fable's, whose two projections
-- are c-map pr₁ / c-map pr₂ (cP-map p₁ / cP-map p₂) by definition. The
-- equivalence proofs are those of ClosedLimits / ClosedLimitsRaised
-- (generator cover, Test.inX-test, closedness; no choice, no FE), moved to
-- Fable's maps by POINTWISE homotopies built with pb-path over the set
-- c Z (resp. cP V₀) from the two component paths, and equiv-homotopy.
--
-- Exports besides the statements (plan section 4, used by stage T):
--   κ-inX, κ-inP, κP-unitP, κP-pointP    generator laws of Fable's κ, κP
--   c-map-equiv, cP-map-equiv            c-map / cP-map send equivalences
--                                        to equivalences
--   cP-map-id, cP-map-compose            pointwise action laws
--   raise-equiv, lower-equiv             h ≃ up h
--   Square.gap-identification,
--   SquareP.gap-identificationP          κ (c-map gap z) / κP (cP-map gap z)
--                                        is the closed square's gap
-- Parameters as in the statements: ORDINARY Q, E, T, P, P-prop; only the
-- levels i, b crisp in AtLevel; no discreteness of P. The reflection is
-- used through ONE instantiation at the level as written (i ⊔ b).
-- Nothing is postulated; no shape, continuity or extensionality.
module SetSourceReflection where

open import Foundations
open import Adjointify using (quasi-inverse)
open import CaptureContext using (Raise; raise; lower; raise-lower)
open import PullbackSetFibers using () renaming (Pullback to PB)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import ClosedReflection using (module Reflection)
open import ClosedLimits using (module Limits; pb-path; equiv-compose)
open import ClosedLimitsRaised using (module AtSupportLimits; raise-set)
open import SetSourceReflectionStatements using (module Gluing; module AtLevel)

-- Equivalences are invariant under pointwise homotopy.
equiv-homotopy : ∀ {a b} {A : Set a} {B : Set b} {k k′ : A → B}
               → ((x : A) → k x ≡ k′ x) → IsEquiv k → IsEquiv k′
equiv-homotopy {k = k} {k′} H e = quasi-inverse {f = k′} (inverse e)
  (λ y → sym (H (inverse e y)) ∙ section e y)
  (λ x → ap (inverse e) (sym (H x)) ∙ retraction e x)

------------------------------------------------------------------------
-- R1, R2, R3 at one level.

module RGluing {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) (P : Set ℓ) (P-prop : IsProp P) where

  open Gluing Q E T P P-prop
    using (module Pullback; Statement-R2; Statement-R3)
  open Reflection Q E T P P-prop

  -- R2: every contractible X, at its own centre.
  R2 : Statement-R2
  R2 (x₀ , contr) = inX x₀ ,
    generators-unique E c-set (λ _ → inX x₀) (λ z → z)
      (λ x → ap inX (contr x)) (λ p → glue x₀ p)

  -- c-map of an equivalence is an equivalence (pointwise laws only).
  c-map-equiv : {X Y : Set ℓ} {h : X → Y} → IsEquiv h → IsEquiv (c-map h)
  c-map-equiv {h = h} e = quasi-inverse {f = c-map h} (c-map (inverse e))
    (λ z → sym (c-map-compose h (inverse e) z)
           ∙ cong-id (λ y → h (inverse e y)) (section e) z)
    (λ z → sym (c-map-compose (inverse e) h z)
           ∙ cong-id (λ x → inverse e (h x)) (retraction e) z)
    where
    cong-id : {W : Set ℓ} (k : W → W) → ((w : W) → k w ≡ w)
            → (z : c W) → c-map k z ≡ z
    cong-id k H = generators-unique E c-set (c-map k) (λ z → z)
      (λ w → c-map-inX k w ∙ ap inX (H w)) (λ p → c-map-inP k p)

  module R1 {X Y Z : Set ℓ} (f : X → Z) (g : Y → Z) where

    open Pullback f g

    -- Generator laws of THE κ.
    inX-point : D → H
    inX-point d = inX (pr₁ d) , inX (pr₂ d) ,
      (c-map-inX g (pr₂ d) ∙ ap inX (snd (snd d)) ∙ sym (c-map-inX f (pr₁ d)))

    inP-point : P → H
    inP-point p = inP p , inP p , (c-map-inP g p ∙ sym (c-map-inP f p))

    κ-inX : (d : D) → κ (inX d) ≡ inX-point d
    κ-inX d = pb-path c-set (c-map-inX pr₁ d) (c-map-inX pr₂ d)

    κ-inP : (p : P) → κ (inP p) ≡ inP-point p
    κ-inP p = pb-path c-set (c-map-inP pr₁ p) (c-map-inP pr₂ p)

    R1 : Statement-R1
    R1 Z-set effective =
      equiv-homotopy (λ z → pb-path c-set refl refl) K.κ-equiv
      where
      module K = Limits.Comparison Q E T P P-prop effective Z-set g f

  R3 : Statement-R3
  R3 X-set Y-set effective h open-equiv closed-equiv =
    Limits.Detection.detect Q E T P P-prop effective X-set Y-set h
      open-equiv closed-equiv

  -- The closed square's gap, for Fable's κ.
  module Square {W X Y Z : Set ℓ} (f : X → Z) (g : Y → Z)
    (l : W → X) (r : W → Y) (sq : (w : W) → g (r w) ≡ f (l w)) where

    open Pullback f g using (D; H; κ; pr₁; pr₂)

    gap : W → D
    gap w = l w , r w , sq w

    closed-square : (z : c W) → c-map g (c-map r z) ≡ c-map f (c-map l z)
    closed-square z =
      sym (c-map-compose g r z)
      ∙ generators-unique E c-set (c-map (λ w → g (r w))) (c-map (λ w → f (l w)))
          (λ w → c-map-inX (λ w′ → g (r w′)) w ∙ ap inX (sq w)
                 ∙ sym (c-map-inX (λ w′ → f (l w′)) w))
          (λ p → c-map-inP (λ w′ → g (r w′)) p
                 ∙ sym (c-map-inP (λ w′ → f (l w′)) p)) z
      ∙ c-map-compose f l z

    closed-gap : c W → H
    closed-gap z = c-map l z , c-map r z , closed-square z

    gap-identification : (z : c W) → κ (c-map gap z) ≡ closed-gap z
    gap-identification z = pb-path c-set
      (sym (c-map-compose pr₁ gap z)) (sym (c-map-compose pr₂ gap z))

------------------------------------------------------------------------
-- R1P, R2P, R3P: sets of level i, support at the level written i ⊔ b.

module RAtLevel {@♭ i b : Level} (Q : Quotients (i ⊔ b))
  (E : Eliminates Q (i ⊔ b)) (T : PropTruncation (i ⊔ b))
  (P : Set (i ⊔ b)) (P-prop : IsProp P) where

  open AtLevel {i} {b} Q E T P P-prop
  open Reflection Q E T P P-prop
  private
    module G = RGluing Q E T P P-prop

  -- h and up h are equivalences together.
  raise-equiv : {V W : Set i} {h : V → W} → IsEquiv h → IsEquiv (up h)
  raise-equiv {h = h} e = quasi-inverse {f = up h}
    (λ r → raise (inverse e (lower r)))
    (λ r → ap raise (section e (lower r)) ∙ raise-lower r)
    (λ r → ap raise (retraction e (lower r)) ∙ raise-lower r)

  lower-equiv : {V W : Set i} {h : V → W} → IsEquiv (up h) → IsEquiv h
  lower-equiv {h = h} e = quasi-inverse {f = h}
    (λ w → lower (inverse e (raise w)))
    (λ w → ap lower (section e (raise w)))
    (λ v → ap lower (retraction e (raise v)))

  -- The pointwise action laws and the action on equivalences.
  cP-map-id : {V : Set i} (z : cP V) → cP-map (λ v → v) z ≡ z
  cP-map-id = generators-unique E c-set (cP-map (λ v → v)) (λ z → z)
    (λ r → c-map-inX (up (λ v → v)) r ∙ ap inX (raise-lower r))
    (λ p → c-map-inP (up (λ v → v)) p)

  cP-map-compose : {U V W : Set i} (g : V → W) (f : U → V) (z : cP U)
                 → cP-map (λ u → g (f u)) z ≡ cP-map g (cP-map f z)
  cP-map-compose g f z = c-map-compose (up g) (up f) z

  cP-map-equiv : {V W : Set i} {h : V → W} → IsEquiv h → IsEquiv (cP-map h)
  cP-map-equiv e = G.c-map-equiv (raise-equiv e)

  R2P : Statement-R2P
  R2P (w₀ , contr) =
    G.R2 (raise w₀ , λ { (raise w) → ap raise (contr w) })

  R3P : Statement-R3P
  R3P {V} {W} V-set W-set effective h open-equiv closed-equiv =
    lower-equiv (G.R3 (raise-set V-set) (raise-set W-set) effective (up h)
      (λ p → raise-equiv (open-equiv p)) closed-equiv)

  module R1P {V₁ V₂ V₀ : Set i} (f : V₁ → V₀) (g : V₂ → V₀) where

    open PullbackP f g

    -- Generator laws of THE κP.
    unitP-point : D₀ → HP
    unitP-point d = unitP (p₁ d) , unitP (p₂ d) ,
      (cP-map-unit g (p₂ d) ∙ ap unitP (snd (snd d)) ∙ sym (cP-map-unit f (p₁ d)))

    pointP-point : P → HP
    pointP-point p = pointP p , pointP p ,
      (cP-map-point g p ∙ sym (cP-map-point f p))

    κP-unitP : (d : D₀) → κP (unitP d) ≡ unitP-point d
    κP-unitP d = pb-path c-set (cP-map-unit p₁ d) (cP-map-unit p₂ d)

    κP-pointP : (p : P) → κP (pointP p) ≡ pointP-point p
    κP-pointP p = pb-path c-set (cP-map-point p₁ p) (cP-map-point p₂ p)

    -- The raised comparison of ClosedLimitsRaised is c-map of the explicit
    -- Raise/pullback equivalence followed by κ; its two component paths
    -- and pb-path over the set cP V₀ move IsEquiv to THE κP.
    R1P : Statement-R1P
    R1P V₀-set effective =
      equiv-homotopy (λ z → pb-path c-set (L.κP-projY z) (L.κP-projX z))
        L.κP-equiv
      where
      module L = AtSupportLimits.Raised {i} {b} Q E T P P-prop effective
        V₀-set g f

  -- The closed square's gap, for THE κP.
  module SquareP {U V₁ V₂ V₀ : Set i} (f : V₁ → V₀) (g : V₂ → V₀)
    (l : U → V₁) (r : U → V₂) (sq : (u : U) → g (r u) ≡ f (l u)) where

    open PullbackP f g using (D₀; HP; κP; p₁; p₂)

    gap : U → D₀
    gap u = l u , r u , sq u

    closed-squareP : (z : cP U) → cP-map g (cP-map r z) ≡ cP-map f (cP-map l z)
    closed-squareP z =
      sym (cP-map-compose g r z)
      ∙ generators-unique E c-set (cP-map (λ u → g (r u))) (cP-map (λ u → f (l u)))
          (λ x → c-map-inX (up (λ u → g (r u))) x ∙ ap inX (ap raise (sq (lower x)))
                 ∙ sym (c-map-inX (up (λ u → f (l u))) x))
          (λ p → c-map-inP (up (λ u → g (r u))) p
                 ∙ sym (c-map-inP (up (λ u → f (l u))) p)) z
      ∙ cP-map-compose f l z

    closed-gapP : cP U → HP
    closed-gapP z = cP-map l z , cP-map r z , closed-squareP z

    gap-identificationP : (z : cP U) → κP (cP-map gap z) ≡ closed-gapP z
    gap-identificationP z = pb-path c-set
      (sym (cP-map-compose p₁ gap z)) (sym (cP-map-compose p₂ gap z))
