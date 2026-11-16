{-# OPTIONS --cohesion --without-K --flat-split #-}

-- From a full relative shape to the accepted Shape₀ interface, by
-- truncating the FIBRES of the carrier.
-- Claude (Fable), 14 November 2026; fable-impl-23 (HANDOFF-38, "Bridge to
-- the accepted Shape₀").
--
-- For a full shape K of A over a crisp discrete B, with carrier
-- q : R → B and F b = Fiber q b, the type
--     R₀ = Σ (b : B) (τ₀ (F b)),   with projection fst,
-- carries a RelativeShapeOver B dB A:
--     unit        k ∘ η,  where k r = (q r , ∣ r , refl ∣₀)
--     unit-over   the ORIGINAL triangle of K (fst ∘ k is q by conversion)
--     universal   for a set-fibred test t, the composite of three
--                 equivalences of boxed whole maps over B:
--                   out of Σ B (τ₀ ∘ F)  →  out of Σ B F    (the truncation;
--                       TruncatedPayload.Over.restrict♭-equiv at F)
--                   out of Σ B F         →  out of R        (R is Σ B F)
--                   out of R             →  out of Σ B A    (K, at t)
--                 The composite IS precomposition with the new unit, by
--                 conversion on both fields.
-- B is only discrete; it is not asked to be a set.
--
-- The carrier is NOT the truncation of R: that would forget the paths of
-- the base, already for the identity projection over a higher discrete B.
--
-- Parameters: a crisp ordinary SetTruncation of the level and crisp
-- same-level function extensionality (for whole-map inverse laws, as in
-- TruncatedPayload). Nothing is postulated and nothing is declared.
module FullToShape0 where

open import Foundations
open import NativeSharp using (box-crisp-path)
open import Adjointify using (quasi-inverse)
open import FlatContext using (right-unit)
open import PullbackSetFibers using (transport; fiber-fst-set)
open import ShapeElim using (module SigmaDiscrete; module FiberDiscrete)
open import ShapeChoice using (FunExtAt)
open import RelativeSliceShape
open import OrdinaryTruncation
open import TruncatedPayload using (module Truncate)
open import SetTruncationDiscrete using (truncation-discrete₀)
open import FullRelativeShape

private
  compose-is-equiv : ∀ {a b c} {X : Set a} {Y : Set b} {Z : Set c}
                   → {f : X → Y} {g : Y → Z}
                   → IsEquiv f → IsEquiv g → IsEquiv (λ x → g (f x))
  compose-is-equiv {f = f} {g} ef eg = quasi-inverse
    (λ z → inverse ef (inverse eg z))
    (λ z → ap g (section ef (inverse eg z)) ∙ section eg z)
    (λ x → ap (inverse ef) (retraction eg (f x)) ∙ retraction ef x)

  homotopic-is-equiv : ∀ {a b} {X : Set a} {Y : Set b} {f g : X → Y}
                     → ((x : X) → f x ≡ g x) → IsEquiv f → IsEquiv g
  homotopic-is-equiv {f = f} {g} h ef = quasi-inverse (inverse ef)
    (λ y → sym (h (inverse ef y)) ∙ section ef y)
    (λ x → ap (inverse ef) (sym (h x)) ∙ retraction ef x)

module Bridge {@♭ ℓ : Level} (@♭ τ : SetTruncation ℓ) (@♭ fe : FunExtAt ℓ)
  {@♭ B : Set ℓ} {@♭ dB : Discrete B} {@♭ A : B → Set ℓ}
  (@♭ K : FullShapeOver B dB A) where

  open SetTruncation τ

  private
    R : Set ℓ
    R = FullOutput.Total K

    q : R → B
    q = FullOutput.projection K

  -- The fibres of the full carrier, and their truncations.
  F : B → Set ℓ
  F b = Fiber q b

  F₀ : B → Set ℓ
  F₀ b = τ₀ (F b)

  R₀ : Set ℓ
  R₀ = Σ B F₀

  F-discrete : (@♭ b : B) → Discrete (F b)
  F-discrete b = FiberDiscrete.discrete dB (FullOutput.total-discrete K) q b

  F₀-discrete : (@♭ b : B) → Discrete (F₀ b)
  F₀-discrete b = truncation-discrete₀ τ (F-discrete b)

  R₀-discrete : Discrete R₀
  R₀-discrete = SigmaDiscrete.discrete dB F₀-discrete

  R₀-set-fibers : SetFibers (fst {B = F₀})
  R₀-set-fibers b = fiber-fst-set b τ₀-set

  -- The map of carriers. Its triangle is refl.
  k : R → R₀
  k r = q r , ∣ r , refl ∣₀

  k-over : (r : R) → fst (k r) ≡ q r
  k-over r = refl

  η₀ : Σ B A → R₀
  η₀ a = k (FullOutput.unit K a)

  -- The original triangle, kept.
  η₀-over : UnitOver B A R₀ fst η₀
  η₀-over a = FullOutput.unit-over K a

  module Against (@♭ D : Set ℓ) (@♭ dD : Discrete D)
    (@♭ t : D → B) (@♭ tf : SetFibers t) where

    private
      module T = Truncate τ fe {B} {dB} {F}

    module O = T.Over D t tf

    -- R is the total of its fibres.
    ι : R → Σ B F
    ι r = q r , r , refl

    along : MapOver (fst {B = F}) t → MapOver q t
    along N = over-map (λ r → function N (ι r)) (λ r → triangle N (ι r))

    back : MapOver q t → MapOver (fst {B = F}) t
    back G = over-map (λ x → function G (fst (snd x)))
                      (λ x → triangle G (fst (snd x)) ∙ snd (snd x))

    along-back : (G : MapOver q t) → along (back G) ≡ G
    along-back G =
      ap (over-map (function G)) (fe (λ r → right-unit (triangle G r)))

    private
      law : (N : MapOver (fst {B = F}) t) (b : B) (w : F b)
          → O.curry (back (along N)) b w ≡ O.curry N b w
      law N .(q r) (r , refl) =
        ap (λ path → function N (q r , r , refl) , path)
           (right-unit (triangle N (q r , r , refl)))

    back-along : (N : MapOver (fst {B = F}) t) → back (along N) ≡ N
    back-along N = ap (O.uncurry {F = F}) (fe (λ b → fe (λ w → law N b w)))

    private
      along♭-back : (y : ♭ (MapOver q t))
                  → flat-map along (flat-map back y) ≡ y
      along♭-back (box G) = box-crisp-path (along-back G)

      back-along♭ : (x : ♭ (MapOver (fst {B = F}) t))
                  → flat-map back (flat-map along x) ≡ x
      back-along♭ (box N) = box-crisp-path (back-along N)

    along♭-equiv : IsEquiv (flat-map along)
    along♭-equiv = quasi-inverse (flat-map back) along♭-back back-along♭

    -- Precomposition with the new unit, and with the unit of K.
    pre₀ : MapOver (fst {B = F₀}) t → MapOver (fst {B = A}) t
    pre₀ = precomposeOver B A R₀ fst η₀ η₀-over D t

    preK : MapOver q t → MapOver (fst {B = A}) t
    preK = FullOutput.pre K D t

    -- The three steps compose to pre₀, on both fields, by conversion.
    same : (M : MapOver (fst {B = F₀}) t)
         → preK (along (O.restrict M)) ≡ pre₀ M
    same M = refl

    private
      factorisation : (x : ♭ (MapOver (fst {B = F₀}) t))
                    → flat-map preK (flat-map along (O.restrict♭ x))
                      ≡ flat-map pre₀ x
      factorisation (box M) = refl

    universal₀ : IsEquiv (flat-map pre₀)
    universal₀ = homotopic-is-equiv factorisation
      (compose-is-equiv
        (compose-is-equiv O.restrict♭-equiv along♭-equiv)
        (FullOutput.universal K D dD t))

  -- The Shape₀ payload on the fibrewise truncation of the full carrier.
  truncated : RelativeShapeOver B dB A
  truncated = shape-over R₀ R₀-discrete fst R₀-set-fibers η₀ η₀-over
    (λ D dD t tf → Against.universal₀ D dD t tf)

  same-carrier : Output.Total truncated ≡ R₀
  same-carrier = refl

  same-projection : (z : R₀) → Output.projection truncated z ≡ fst z
  same-projection z = refl

  same-unit : (a : Σ B A) → Output.unit truncated a ≡ k (FullOutput.unit K a)
  same-unit a = refl

  same-unit-over : (a : Σ B A)
                 → Output.unit-over truncated a ≡ FullOutput.unit-over K a
  same-unit-over a = refl

  -- The selected fibre is the truncation of the selected full fibre,
  -- with the unit carried along.
  fibre-in : (b : B) → F₀ b → Output.family truncated b
  fibre-in b z = (b , z) , refl

  fibre-out : (b : B) → Output.family truncated b → F₀ b
  fibre-out b (z , e) = transport F₀ e (snd z)

  fibre-out-in : (b : B) (z : F₀ b) → fibre-out b (fibre-in b z) ≡ z
  fibre-out-in b z = refl

  fibre-in-out : (b : B) (w : Output.family truncated b)
               → fibre-in b (fibre-out b w) ≡ w
  fibre-in-out b (z , refl) = refl

  fibre-out-equiv : (b : B) → IsEquiv (fibre-out b)
  fibre-out-equiv b =
    quasi-inverse (fibre-in b) (fibre-out-in b) (fibre-in-out b)

  private
    carry : (r : R) {b : B} (e : q r ≡ b)
          → transport F₀ e ∣ r , refl ∣₀ ≡ ∣ r , e ∣₀
    carry r refl = refl

  fibre-unit : (b : B) (a : A b)
             → fibre-out b (Output.family-unit truncated b a)
               ≡ ∣ FullOutput.family-unit K b a ∣₀
  fibre-unit b a =
    carry (FullOutput.unit K (b , a)) (FullOutput.unit-over K (b , a))
