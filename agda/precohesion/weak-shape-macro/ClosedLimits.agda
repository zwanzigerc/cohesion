{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE ORDINARY CLOSED REFLECTOR: FINITE LIMITS AND JOINT DETECTION.
-- Opus, 14 November 2026; opus-closed-limits-01, implementing
-- OPUS-CLOSED-LIMITS-AND-DETECTION-RELEASE-01.txt, items 1 and 2, i.e.
-- SMALL-SET-OPEN-CLOSED-GLUING-01 sections 2 and 3 (Fable's rederivation:
-- FABLE-SET-PROOF-ASSESSMENT-01 sections 2 and 4.3), on the M22 operations
-- of ClosedReflection.Reflection Q E T P P-prop.
--
-- Parameters (all ORDINARY, as in Reflection): a quotient structure Q at
-- level ℓ, its same-level elimination E, a propositional truncation T at ℓ,
-- a proposition P : Set ℓ, and evidence  effective : Effective Q  (derived
-- by QuotientEffectivity.OneRow, or supplied). Sets, maps and witnesses
-- below are ordinary.
--
-- 1. FINITE LIMITS. For f : X → Z, g : Y → Z with Z a set, and the native
--    Pullback f g = Σ (y : Y). Σ (x : X). f x ≡ g y (PullbackSetFibers):
--      κ : c (Pullback f g) → Pullback (c-map f) (c-map g)
--      κ z = c-map projY z , c-map projX z , κ-square z
--    — its first two components ARE c-map projY and c-map projX (κ-projY,
--    κ-projX are refl); the third comes from generators-unique, with
--    c-map-inX twice and the original pullback path at inX, c-map-inP at inP.
--    κ-inX, κ-inP: the two generator laws. κ-injective: by generator-cover,
--    Test.inX-test on X and Y, and closedness under P. κ-equiv : IsEquiv κ:
--    fibres are propositions (SmallPropositions.injective-fibres), and a
--    point of each fibre is obtained by proposition-valued elimination of
--    the two generator covers and Test.inX-test on Z. No choice, no uniform
--    representative. terminal-equiv: c 1 ≃ 1 for the terminal set 1 = One ℓ
--    (and inX-terminal-equiv).
--    c-map-cong: pointwise congruence of c-map, by the two generators.
--    Gap identification (for the later closed-square proof): for a
--    commutative square l, r, sq over f, g with gap h, κ (c-map h z) is the
--    closed square's gap at z (closed-gap-identification), by the two
--    projection laws, c-map-compose and sethood of c Z.
-- 2. JOINT DETECTION. For h : X → Y between sets: from an ORDINARY
--    open : P → IsEquiv h and an ORDINARY IsEquiv (c-map h), IsEquiv h
--    (detect). detect-product takes IsEquiv (id_P × h) instead, whose
--    inverse at (p , y) projects to the inverse under p (open-from-product).
--
-- Nothing is postulated. NO shape, continuity, Nullstellensatz, choice,
-- function or propositional extensionality is used; every law is pointwise.
-- The only truncation used is the same-level T; every elimination is into
-- a proposition of level ℓ. These are left-exactness facts for c on sets;
-- nothing is claimed about shape being left exact. Not --safe:
-- ClosedReflection has --flat-split (its discreteness part), and so does
-- TotalBridge (Σ-set).
module ClosedLimits where

open import Foundations
open import Adjointify using (quasi-inverse)
open import PullbackSetFibers using (Pullback)
open import TotalBridge using (Σ-set)
open import SmallPropositions using (prop-is-set; injective-fibres)
open import TruncationDiscrete using (_⊎_; inl; inr)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates; Effective)
open import ClosedReflection using (module Reflection)
open import QuotientTruncations using (One; one)

------------------------------------------------------------------------
-- Small path lemmas on the native pullback.

module _ {a} {X Y Z : Set a} {f : X → Z} {g : Y → Z} where

  -- Two points of a pullback over a SET agree when their projections do.
  pb-path : IsSet Z → {y y′ : Y} {x x′ : X} {e : f x ≡ g y} {e′ : f x′ ≡ g y′}
          → y ≡ y′ → x ≡ x′
          → _≡_ {A = Pullback f g} (y , x , e) (y′ , x′ , e′)
  pb-path Z-set {y} {.y} {x} {.x} {e} {e′} refl refl =
    ap (λ q → y , x , q) (Z-set (f x) (g y) e e′)

  pb-set : IsSet X → IsSet Y → IsSet Z → IsSet (Pullback f g)
  pb-set X-set Y-set Z-set =
    Σ-set Y-set (λ y → Σ-set X-set (λ x → prop-is-set (Z-set (f x) (g y))))

-- An equivalence is injective.
equiv-injective : ∀ {a b} {A : Set a} {B : Set b} {h : A → B}
                → IsEquiv h → {x x′ : A} → h x ≡ h x′ → x ≡ x′
equiv-injective e {x} {x′} q =
  sym (retraction e x) ∙ ap (inverse e) q ∙ retraction e x′

-- Equivalences compose.
equiv-compose : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              → {f : A → B} {g : B → C} → IsEquiv f → IsEquiv g
              → IsEquiv (λ x → g (f x))
equiv-compose {f = f} {g} ef eg = quasi-inverse
  (λ z → inverse ef (inverse eg z))
  (λ z → ap g (section ef (inverse eg z)) ∙ section eg z)
  (λ x → ap (inverse ef) (retraction eg (f x)) ∙ retraction ef x)

-- An inhabited proposition is contractible; for fibres this is IsEquiv.
inhabited-prop-equiv : ∀ {a b} {A : Set a} {B : Set b} {h : A → B}
                     → ((y : B) → IsProp (Fiber h y))
                     → ((y : B) → Fiber h y) → IsEquiv h
inhabited-prop-equiv fib-prop point y = point y , fib-prop y (point y)

------------------------------------------------------------------------

module Limits {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) (P : Set ℓ) (P-prop : IsProp P)
  (effective : Effective Q) where

  open PropTruncation T
  open Reflection Q E T P P-prop
  open Test effective using (inX-test)

  -- Under P any two points of a reflection agree.
  by-closed : {W : Set ℓ} → P → (u v : c W) → u ≡ v
  by-closed p u v = sym (snd (closed p) u) ∙ snd (closed p) v

  ----------------------------------------------------------------------
  -- Pointwise congruence and the terminal set.

  c-map-cong : {X Y : Set ℓ} (f g : X → Y) → ((x : X) → f x ≡ g x)
             → (z : c X) → c-map f z ≡ c-map g z
  c-map-cong f g H = generators-unique E c-set (c-map f) (c-map g)
    (λ x → c-map-inX f x ∙ ap inX (H x) ∙ sym (c-map-inX g x))
    (λ p → c-map-inP f p ∙ sym (c-map-inP g p))

  -- The terminal set at level ℓ is One ℓ (QuotientTruncations), a record
  -- with eta, so every point is `one` by conversion.
  terminal-contraction : (z : c (One ℓ)) → inX one ≡ z
  terminal-contraction = generators-unique E c-set (λ _ → inX one) (λ z → z)
    (λ _ → refl) (λ p → glue one p)

  terminal-contr : IsContr (c (One ℓ))
  terminal-contr = inX one , terminal-contraction

  -- The terminal comparison c 1 → 1 is an equivalence, with inverse inX.
  to-one : c (One ℓ) → One ℓ
  to-one _ = one

  terminal-equiv : IsEquiv to-one
  terminal-equiv = quasi-inverse (λ _ → inX one) (λ _ → refl)
    terminal-contraction

  inX-terminal-equiv : IsEquiv (inX {One ℓ})
  inX-terminal-equiv = quasi-inverse (λ _ → one) terminal-contraction
    (λ _ → refl)

  ----------------------------------------------------------------------
  -- 1. The canonical pullback comparison.

  module Comparison {X Y Z : Set ℓ} (Z-set : IsSet Z)
    (f : X → Z) (g : Y → Z) where

    D : Set ℓ
    D = Pullback f g

    H : Set ℓ
    H = Pullback (c-map f) (c-map g)

    H-set : IsSet H
    H-set = pb-set c-set c-set c-set

    -- The projections of D, at their exact types.
    projY : D → Y
    projY = fst

    projX : D → X
    projX d = fst (snd d)

    pb-square : (d : D) → f (projX d) ≡ g (projY d)
    pb-square d = snd (snd d)

    κ-square : (z : c D) → c-map f (c-map projX z) ≡ c-map g (c-map projY z)
    κ-square = generators-unique E c-set
      (λ z → c-map f (c-map projX z)) (λ z → c-map g (c-map projY z))
      (λ d → ap (c-map f) (c-map-inX projX d) ∙ c-map-inX f (projX d)
             ∙ ap inX (pb-square d)
             ∙ sym (ap (c-map g) (c-map-inX projY d) ∙ c-map-inX g (projY d)))
      (λ p → ap (c-map f) (c-map-inP projX p) ∙ c-map-inP f p
             ∙ sym (ap (c-map g) (c-map-inP projY p) ∙ c-map-inP g p))

    -- THE comparison.
    κ : c D → H
    κ z = c-map projY z , c-map projX z , κ-square z

    κ-projY : (z : c D) → fst (κ z) ≡ c-map projY z
    κ-projY z = refl

    κ-projX : (z : c D) → fst (snd (κ z)) ≡ c-map projX z
    κ-projX z = refl

    -- The generator laws.
    inX-point : D → H
    inX-point d = inX (projY d) , inX (projX d) ,
      (c-map-inX f (projX d) ∙ ap inX (pb-square d) ∙ sym (c-map-inX g (projY d)))

    inP-point : P → H
    inP-point p = inP p , inP p , (c-map-inP f p ∙ sym (c-map-inP g p))

    κ-inX : (d : D) → κ (inX d) ≡ inX-point d
    κ-inX d = pb-path c-set (c-map-inX projY d) (c-map-inX projX d)

    κ-inP : (p : P) → κ (inP p) ≡ inP-point p
    κ-inP p = pb-path c-set (c-map-inP projY p) (c-map-inP projX p)

    -- Under P every point of H is any other.
    H-by-closed : P → (u v : H) → u ≡ v
    H-by-closed p u v = pb-path c-set (by-closed p _ _) (by-closed p _ _)

    -- Injectivity.
    private
      on-generators : (d d′ : D) → κ (inX d) ≡ κ (inX d′) → inX d ≡ inX d′
      on-generators d d′ q =
        ∥-rec (c-set _ _) (λ ty → ∥-rec (c-set _ _) (λ tx → both ty tx) x-test) y-test
        where
        y-eq : inX (projY d) ≡ inX (projY d′)
        y-eq = sym (c-map-inX projY d) ∙ ap fst q ∙ c-map-inX projY d′

        x-eq : inX (projX d) ≡ inX (projX d′)
        x-eq = sym (c-map-inX projX d) ∙ ap (λ t → fst (snd t)) q
               ∙ c-map-inX projX d′

        y-test = inX-test (projY d) (projY d′) y-eq
        x-test = inX-test (projX d) (projX d′) x-eq

        both : (projY d ≡ projY d′) ⊎ P → (projX d ≡ projX d′) ⊎ P
             → inX d ≡ inX d′
        both (inl ey) (inl ex) = ap inX (pb-path Z-set ey ex)
        both (inr p) _ = by-closed p _ _
        both (inl _) (inr p) = by-closed p _ _

    κ-injective : (u v : c D) → κ u ≡ κ v → u ≡ v
    κ-injective u v q =
      ∥-rec (c-set u v)
        (λ cu → ∥-rec (c-set u v) (λ cv → cases cu cv) (generator-cover v))
        (generator-cover u)
      where
      cases : Fiber inX u ⊎ Fiber inP u → Fiber inX v ⊎ Fiber inP v → u ≡ v
      cases (inl (d , eu)) (inl (d′ , ev)) =
        sym eu ∙ on-generators d d′ (ap κ eu ∙ q ∙ sym (ap κ ev)) ∙ ev
      cases (inr (p , _)) _ = by-closed p u v
      cases (inl _) (inr (p , _)) = by-closed p u v

    κ-fibre-prop : (w : H) → IsProp (Fiber κ w)
    κ-fibre-prop = injective-fibres κ H-set κ-injective

    -- A point of every fibre, by proposition-valued elimination.
    κ-point : (w : H) → Fiber κ w
    κ-point (v , u , e) =
      ∥-rec (κ-fibre-prop w)
        (λ cv → ∥-rec (κ-fibre-prop w) (λ cu → cases cv cu) (generator-cover u))
        (generator-cover v)
      where
      w : H
      w = v , u , e

      from-P : P → Fiber κ w
      from-P p = inP p , H-by-closed p _ _

      cases : Fiber inX v ⊎ Fiber inP v → Fiber inX u ⊎ Fiber inP u → Fiber κ w
      cases (inl (y , ev)) (inl (x , eu)) =
        ∥-rec (κ-fibre-prop w) found (inX-test (f x) (g y) z-eq)
        where
        z-eq : inX (f x) ≡ inX (g y)
        z-eq = sym (c-map-inX f x) ∙ ap (c-map f) eu ∙ e
               ∙ sym (ap (c-map g) ev) ∙ c-map-inX g y

        found : (f x ≡ g y) ⊎ P → Fiber κ w
        found (inl r) = inX (y , x , r) ,
          pb-path c-set (c-map-inX projY (y , x , r) ∙ ev)
                        (c-map-inX projX (y , x , r) ∙ eu)
        found (inr p) = from-P p
      cases (inr (p , _)) _ = from-P p
      cases (inl _) (inr (p , _)) = from-P p

    κ-equiv : IsEquiv κ
    κ-equiv = inhabited-prop-equiv κ-fibre-prop κ-point

  ----------------------------------------------------------------------
  -- The closed square's gap and c of the gap (for the later square proof).

  module Square {W X Y Z : Set ℓ} (Z-set : IsSet Z)
    (f : X → Z) (g : Y → Z)
    (l : W → X) (r : W → Y) (sq : (w : W) → f (l w) ≡ g (r w)) where

    open Comparison Z-set f g using (D; H; κ; projY; projX)

    gap : W → D
    gap w = r w , l w , sq w

    closed-square : (z : c W) → c-map f (c-map l z) ≡ c-map g (c-map r z)
    closed-square z =
      sym (c-map-compose f l z)
      ∙ c-map-cong (λ w → f (l w)) (λ w → g (r w)) sq z
      ∙ c-map-compose g r z

    closed-gap : c W → H
    closed-gap z = c-map r z , c-map l z , closed-square z

    -- κ ∘ c-map gap is the closed gap, pointwise: the two projection laws,
    -- c-map-compose, and sethood of c Z.
    closed-gap-identification : (z : c W) → κ (c-map gap z) ≡ closed-gap z
    closed-gap-identification z = pb-path c-set
      (sym (c-map-compose projY gap z))
      (sym (c-map-compose projX gap z))

  ----------------------------------------------------------------------
  -- 2. Joint detection.

  module Detection {X Y : Set ℓ} (X-set : IsSet X) (Y-set : IsSet Y)
    (h : X → Y) where

    module _ (open-equiv : P → IsEquiv h) (closed-equiv : IsEquiv (c-map h))
      where

      h-injective : (x x′ : X) → h x ≡ h x′ → x ≡ x′
      h-injective x x′ q =
        ∥-rec (X-set x x′) branch (inX-test x x′ gen-eq)
        where
        gen-eq : inX x ≡ inX x′
        gen-eq = equiv-injective closed-equiv
          (c-map-inX h x ∙ ap inX q ∙ sym (c-map-inX h x′))

        branch : (x ≡ x′) ⊎ P → x ≡ x′
        branch (inl e) = e
        branch (inr p) = equiv-injective (open-equiv p) q

      h-fibre-prop : (y : Y) → IsProp (Fiber h y)
      h-fibre-prop = injective-fibres h Y-set h-injective

      h-point : (y : Y) → Fiber h y
      h-point y =
        ∥-rec (h-fibre-prop y) cases (generator-cover z)
        where
        z : c X
        z = inverse closed-equiv (inX y)

        from-P : P → Fiber h y
        from-P p = fst (open-equiv p y)

        cases : Fiber inX z ⊎ Fiber inP z → Fiber h y
        cases (inl (x , ex)) =
          ∥-rec (h-fibre-prop y) found (inX-test (h x) y y-eq)
          where
          y-eq : inX (h x) ≡ inX y
          y-eq = sym (c-map-inX h x) ∙ ap (c-map h) ex
                 ∙ section closed-equiv (inX y)

          found : (h x ≡ y) ⊎ P → Fiber h y
          found (inl r) = x , r
          found (inr p) = from-P p
        cases (inr (p , _)) = from-P p

      detect : IsEquiv h
      detect = inhabited-prop-equiv h-fibre-prop h-point

    -- The open product map and its restriction under p.
    id×h : P × X → P × Y
    id×h (p , x) = p , h x

    private
      to : {p : P} {y : Y} → Fiber id×h (p , y) → Fiber h y
      to (px , q) = snd px , ap snd q

      from : (p : P) {y : Y} → Fiber h y → Fiber id×h (p , y)
      from p (x , r) = (p , x) , ap (λ y′ → p , y′) r

      to-from : (p : P) {y : Y} (w : Fiber h y) → to (from p w) ≡ w
      to-from p (x , refl) = refl

    -- Under p, the fibre of h at y is a retract of the fibre of id×h at
    -- (p , y): the inverse of id×h at (p , y), projected.
    open-from-product : IsEquiv id×h → P → IsEquiv h
    open-from-product e p y =
      to (fst (e (p , y))) ,
      λ w → ap to (snd (e (p , y)) (from p w)) ∙ to-from p w

    detect-product : IsEquiv id×h → IsEquiv (c-map h) → IsEquiv h
    detect-product e = detect (open-from-product e)
