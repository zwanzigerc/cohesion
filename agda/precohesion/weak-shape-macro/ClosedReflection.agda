{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The closed reflection of a set at a proposition P, as ONE small quotient:
--
--   c X = (X ⊎ P) / R,     R s t = ∥ (s ≡ t) ⊎ P ∥.
--
-- It is the set pushout of X ← X × P → P, kept at the level of X and P.
-- Claude (Fable), 14 November 2026; fable-impl-22 (HANDOFF-37, item 3;
-- SMALL-CLOSED-REFLECTION-NATIVE-ROUTE-01, sections 1 to 3, whose recipe
-- this follows; SET-MAIN-FIXED-DATA-AND-STAGING-01, for the uses of the
-- two-generator property).
--
-- Nothing is postulated. THE QUOTIENT IS SUPPLIED: every definition is
-- under Q : Quotients ℓ with E : Eliminates Q ℓ and a propositional
-- truncation T of the same level (any one: the one derived from Q, or the
-- one that fable-impl-20 takes). Ordinary set theory with one fixed
-- proposition; no shape is involved, and nothing here says that any shape
-- is preserved.
--
-- WHAT IS PROVED, for X : Set ℓ and a proposition P : Set ℓ (module
-- Reflection):
--   inX, inP, glue            the two generators and their identification
--   closed                    under P the carrier is contractible
--   Cocone.extend, -inX, -inP the TWO-GENERATOR PROPERTY: a map X → Y and
--                             a map P → Y into a SET Y that agree on
--                             X × P extend to c X, with both unit laws.
--                             Y need not be closed.
--   generators-unique         two maps c X → Y into a set that agree on
--                             both generators agree
--   Reflect.reflect, -unit,   the reflection property: for a CLOSED set Y a
--   closed-unique             map X → Y extends along inX, uniquely
--   c-map, with its laws      the action on maps, on both generators, on
--                             the identity and on composites
--   generator-cover           every point is merely one of the generators
--   Test.inX-test             equal generators of X come from equal points
--                             or from P; needs evidence of effectivity
-- For a target Y of another level w the three universal properties take
-- the certificates of that level: Eliminates Q w and PropRecInto T w. With
-- T derived from Q the second is prop-rec-into of the first.
--
-- NO EXTENSIONALITY is used in this module. Every law is pointwise. A
-- caller who wants an identification of functions, or an equivalence of
-- function types, supplies function extensionality at the levels concerned
-- (SMALL-CLOSED-REFLECTION-NATIVE-ROUTE-01, end of section 2).
--
-- DISCRETENESS (module Discreteness). If all the data are crisp and X and P
-- are discrete, c X is discrete. The lift c X → ♭ (c X) is defined on
-- representatives through the stored inverses of the two counits and
-- descends because ♭ (c X) is a set; the one identification that it needs
-- between boxed classes is box-crisp-path of `sound` at CRISP
-- representatives and a CRISP point of P. No ordinary path and no ordinary
-- representative is boxed, and no rule that ♭ preserves quotients is used.
-- For a set X that is not discrete the first part still applies and this
-- part says nothing.
--
-- The sum and its discreteness are those of TruncationDiscrete
-- (fable-impl-20); that import is why this module has --flat-split.
module ClosedReflection where

open import Foundations
open import NativeSharp using (transport; box-crisp-path)
open import NativeFlatIdentity using (flat-set)
open import DiscretePullback using (counit-section-discrete)
open import TruncationDiscrete using (_⊎_; inl; inr; sum-discrete)
open import OrdinaryTruncation
open import SmallQuotient
open import QuotientTruncations using (One; one; module Representatives)

-- Closed at P: contractible as soon as P holds.
Closed : ∀ {ℓ w} → Set ℓ → Set w → Set (ℓ ⊔ w)
Closed P Y = P → IsContr Y

------------------------------------------------------------------------
-- 1. The ordinary construction.

module Reflection {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) (P : Set ℓ) (P-prop : IsProp P) where

  open Quotients Q
  open PropTruncation T
  open Induction Q E

  module _ (X : Set ℓ) where

    Sum : Set ℓ
    Sum = X ⊎ P

    private
      flip : {s t : Sum} → (s ≡ t) ⊎ P → (t ≡ s) ⊎ P
      flip (inl e) = inl (sym e)
      flip (inr p) = inr p

      combine : {s t u : Sum} → (s ≡ t) ⊎ P → (t ≡ u) ⊎ P
              → ∥ (s ≡ u) ⊎ P ∥
      combine (inl e) (inl e′) = ∣ inl (e ∙ e′) ∣
      combine (inl _) (inr p) = ∣ inr p ∣
      combine (inr p) _ = ∣ inr p ∣

    relation : EquivRel Sum
    relation = record
      { _≈_ = λ s t → ∥ (s ≡ t) ⊎ P ∥
      ; ≈-prop = λ _ _ → squash
      ; ≈-refl = λ _ → ∣ inl refl ∣
      ; ≈-sym = λ _ _ → ∥-map flip
      ; ≈-trans = λ _ _ _ r r′ →
          ∥-rec squash (λ a → ∥-rec squash (combine a) r′) r
      }

    c : Set ℓ
    c = Sum / relation

  module _ {X : Set ℓ} where

    inX : X → c X
    inX x = [ inl x ]

    inP : P → c X
    inP p = [ inr p ]

    glue : (x : X) (p : P) → inX x ≡ inP p
    glue x p = sound (inl x) (inr p) ∣ inr p ∣

    c-set : IsSet (c X)
    c-set = /-set

    -- Under P every class is the class of the point of P.
    closed : Closed P (c X)
    closed p = inP p ,
      /-ind (λ z → inP p ≡ z) (λ z → /-set (inP p) z)
        (λ s → sound (inr p) s ∣ inr p ∣)

    -- The two-generator property against sets of level w.
    module Cocone {w : Level} (E′ : Eliminates Q w) (into : PropRecInto T w)
      {Y : Set w} (Y-set : IsSet Y)
      (f : X → Y) (g : P → Y) (h : (x : X) (p : P) → f x ≡ g p) where

      private
        on-sum : Sum X → Y
        on-sum (inl x) = f x
        on-sum (inr p) = g p

        to-g : (p : P) (s : Sum X) → on-sum s ≡ g p
        to-g p (inl x) = h x p
        to-g p (inr p′) = ap g (P-prop p′ p)

        step : {s t : Sum X} → (s ≡ t) ⊎ P → on-sum s ≡ on-sum t
        step (inl e) = ap on-sum e
        step {s} {t} (inr p) = to-g p s ∙ sym (to-g p t)

        respects : (s t : Sum X) → ∥ (s ≡ t) ⊎ P ∥ → on-sum s ≡ on-sum t
        respects s t = into (Y-set (on-sum s) (on-sum t)) step

      extend : c X → Y
      extend = Eliminates./-rec E′ Y-set on-sum respects

      extend-inX : (x : X) → extend (inX x) ≡ f x
      extend-inX x = Eliminates./-rec-unit E′ Y-set on-sum respects (inl x)

      extend-inP : (p : P) → extend (inP p) ≡ g p
      extend-inP p = Eliminates./-rec-unit E′ Y-set on-sum respects (inr p)

    generators-unique : {w : Level} (E′ : Eliminates Q w) {Y : Set w}
                      → IsSet Y → (u v : c X → Y)
                      → ((x : X) → u (inX x) ≡ v (inX x))
                      → ((p : P) → u (inP p) ≡ v (inP p))
                      → (z : c X) → u z ≡ v z
    generators-unique E′ Y-set u v on-X on-P =
      Eliminates./-unique E′ Y-set u v on-both
      where
      on-both : (s : Sum X) → u [ s ] ≡ v [ s ]
      on-both (inl x) = on-X x
      on-both (inr p) = on-P p

    -- The reflection property: closed sets see c X as they see X.
    module Reflect {w : Level} (E′ : Eliminates Q w) (into : PropRecInto T w)
      {Y : Set w} (Y-set : IsSet Y) (Y-closed : Closed P Y) (f : X → Y)
      where

      private
        module C = Cocone E′ into Y-set f
          (λ p → fst (Y-closed p))
          (λ x p → sym (snd (Y-closed p) (f x)))

      reflect : c X → Y
      reflect = C.extend

      reflect-unit : (x : X) → reflect (inX x) ≡ f x
      reflect-unit = C.extend-inX

    closed-unique : {w : Level} (E′ : Eliminates Q w) {Y : Set w}
                  → IsSet Y → Closed P Y → (u v : c X → Y)
                  → ((x : X) → u (inX x) ≡ v (inX x))
                  → (z : c X) → u z ≡ v z
    closed-unique E′ Y-set Y-closed u v on-X =
      generators-unique E′ Y-set u v on-X
        (λ p → sym (snd (Y-closed p) (u (inP p)))
               ∙ snd (Y-closed p) (v (inP p)))

    -- Every point is merely a generator.
    generator-cover : (z : c X) → ∥ Fiber inX z ⊎ Fiber inP z ∥
    generator-cover z =
      ∥-map sort (Representatives.representative Q E T z)
      where
      sort : Fiber ([_] {R = relation X}) z → Fiber inX z ⊎ Fiber inP z
      sort (inl x , e) = inl (x , e)
      sort (inr p , e) = inr (p , e)

  -- The action on maps, by the two-generator property at level ℓ.
  module _ {X X′ : Set ℓ} (f : X → X′) where

    private
      module M = Cocone E (own-level T) c-set
        (λ x → inX (f x)) inP (λ x p → glue (f x) p)

    c-map : c X → c X′
    c-map = M.extend

    c-map-inX : (x : X) → c-map (inX x) ≡ inX (f x)
    c-map-inX = M.extend-inX

    c-map-inP : (p : P) → c-map (inP p) ≡ inP p
    c-map-inP = M.extend-inP

  c-map-id : {X : Set ℓ} (z : c X) → c-map (λ x → x) z ≡ z
  c-map-id = generators-unique E c-set (c-map (λ x → x)) (λ z → z)
    (c-map-inX (λ x → x)) (c-map-inP (λ x → x))

  c-map-compose : {X X′ X″ : Set ℓ} (g : X′ → X″) (f : X → X′) (z : c X)
                → c-map (λ x → g (f x)) z ≡ c-map g (c-map f z)
  c-map-compose g f =
    generators-unique E c-set (c-map (λ x → g (f x)))
      (λ z → c-map g (c-map f z))
      (λ x → c-map-inX (λ x′ → g (f x′)) x
             ∙ sym (ap (c-map g) (c-map-inX f x) ∙ c-map-inX g (f x)))
      (λ p → c-map-inP (λ x′ → g (f x′)) p
             ∙ sym (ap (c-map g) (c-map-inP f p) ∙ c-map-inP g p))

  -- The equality test on the generators of X, from evidence of
  -- effectivity (derived in QuotientEffectivity, or supplied).
  module Test (effective : Effective Q) {X : Set ℓ} where

    private
      code : X → Sum X → Set ℓ
      code x (inl x′) = x ≡ x′
      code x (inr _) = One ℓ

      inl-injective : {x x′ : X} → _≡_ {A = Sum X} (inl x) (inl x′)
                    → x ≡ x′
      inl-injective {x} q = transport (code x) q refl

      strip : {x x′ : X} → (_≡_ {A = Sum X} (inl x) (inl x′)) ⊎ P
            → (x ≡ x′) ⊎ P
      strip (inl q) = inl (inl-injective q)
      strip (inr p) = inr p

    inX-test : (x x′ : X) → inX x ≡ inX x′ → ∥ (x ≡ x′) ⊎ P ∥
    inX-test x x′ e = ∥-map strip (effective (inl x) (inl x′) e)

------------------------------------------------------------------------
-- 2. Discreteness, for crisp data.

module Discreteness {@♭ ℓ : Level} (@♭ Q : Quotients ℓ)
  (@♭ E : Eliminates Q ℓ) (@♭ T : PropTruncation ℓ)
  (@♭ P : Set ℓ) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  {@♭ X : Set ℓ} (@♭ dX : Discrete X) where

  open Quotients Q
  open Eliminates E
  open PropTruncation T
  open Reflection Q E T P P-prop

  private
    dS : Discrete (Sum X)
    dS = sum-discrete dX dP

    class : Sum X → c X
    class = [_]

    lift-point : Sum X → ♭ (c X)
    lift-point s = flat-map class (inverse dS s)

    -- Three ordinary points of flat types; their contents are crisp.
    boxed-glue : (u v : ♭ (Sum X)) (w : ♭ P)
               → flat-map class u ≡ flat-map class v
    boxed-glue (box s) (box t) (box p) =
      box-crisp-path (sound s t ∣ inr p ∣)

    flat-c-set : IsSet (♭ (c X))
    flat-c-set = flat-set /-set

    step : {s t : Sum X} → (s ≡ t) ⊎ P → lift-point s ≡ lift-point t
    step (inl e) = ap lift-point e
    step {s} {t} (inr p) =
      boxed-glue (inverse dS s) (inverse dS t) (inverse dP p)

    respects : (s t : Sum X) → ∥ (s ≡ t) ⊎ P ∥
             → lift-point s ≡ lift-point t
    respects s t = ∥-rec (flat-c-set (lift-point s) (lift-point t)) step

    lift : c X → ♭ (c X)
    lift = /-rec flat-c-set lift-point respects

    lift-section : (z : c X) → counit (lift z) ≡ z
    lift-section = /-unique /-set (λ z → counit (lift z)) (λ z → z)
      (λ s → ap counit (/-rec-unit flat-c-set lift-point respects s)
             ∙ flat-map-counit class (inverse dS s)
             ∙ ap class (section dS s))

  discrete : Discrete (c X)
  discrete = counit-section-discrete lift lift-section
