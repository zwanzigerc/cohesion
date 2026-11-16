{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The closed payload of the whole-context macro gives terminal-style shape
-- data. Claude (Fable), 12 November 2026; fable-impl-01.
--
-- For a closed X : Set ℓ the macro declares one constant K : Closed X, a
-- relative reflection over the one-point context. This module derives
-- ShapeData X from it, in two steps.
--
--   Existence X K        carrier, unit, recursor and its computation rule.
--                        Uses K only. The statements of the global axioms
--                        (comparison maps, points-to-pieces) need no more.
--   Bridge fe X K        adds uniqueness and assembles ShapeData X. Uses
--                        function extensionality at level ℓ as a crisp
--                        hypothesis: maps out of  Σ (CrispUnitAt ℓ) A  are
--                        compared pointwise by matching on the point, and
--                        CrispUnitAt has no eta rule.
--
-- Nothing is postulated.
module ClosedBridge where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; end-at; unit-at-discrete; unpack-unit-at; Raise; raise)
import RelativeSliceShape as R
open R using (MapOver; over-map; function; triangle)
open import PullbackSetFibers using (retract-set; left-inverse)
open import NativeSharp using (box-crisp-path)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion

module _ {@♭ ℓ : Level} where

  private
    U : Set ℓ
    U = CrispUnitAt ℓ

    to-end : (γ : U) → γ ≡ end-at
    to-end end-at = refl

    from-end : (γ : U) → end-at ≡ γ
    from-end end-at = refl

    U-prop : IsProp U
    U-prop end-at end-at = refl

    prop-set : ∀ {a} {A : Set a} → IsProp A → IsSet A
    prop-set {A = A} h x y u v = lemma u ∙ sym (lemma v)
      where
      lemma : {z : A} (w : x ≡ z) → w ≡ sym (h x x) ∙ h x z
      lemma refl = sym (left-inverse (h x x))

    U-set : IsSet U
    U-set = prop-set U-prop

  module Existence (@♭ X : Set ℓ) (@♭ K : Closed X) where

    A : U → Set ℓ
    A = unpack-unit-at (Raise ℓ X)

    T : Set ℓ
    T = R.Output.Total K

    p : T → U
    p = R.Output.projection K

    u : Σ U A → T
    u = R.Output.unit K

    uo : (a : Σ U A) → p (u a) ≡ fst a
    uo = R.Output.unit-over K

    η₀ : X → T
    η₀ x = u (end-at , raise x)

    T-set : IsSet T
    T-set = retract-set {B = R.Output.family K end-at}
      (λ z → z , to-end (p z)) fst (λ _ → refl)
      (R.Output.family-set K end-at)

    -- A discrete set D as a target over the one-point context.
    module Target (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

      q : D → U
      q _ = end-at

      q-set-fibers : R.SetFibers q
      q-set-fibers γ = retract-set fst (λ d → d , U-prop end-at γ)
        (λ { (d , e) → ap (λ e′ → d , e′) (U-set end-at γ (U-prop end-at γ) e) })
        D-set

      over : (X → D) → MapOver (fst {B = A}) q
      over f = over-map (λ { (end-at , raise x) → f x }) (λ { (end-at , _) → refl })

      rec₀ : (@♭ f : X → D) → T → D
      rec₀ f = function (R.Output.factor K D D-discrete q q-set-fibers (over f))

      rec₀-η : (@♭ f : X → D) (x : X) → rec₀ f (η₀ x) ≡ f x
      rec₀-η f x = R.Output.factor-on-unit K D D-discrete q q-set-fibers (over f)
        (end-at , raise x)

    -- Points-to-pieces for the closed payload.
    points-to-pieces₀ : ♭ X → T
    points-to-pieces₀ v = η₀ (counit v)

  module Bridge (@♭ fe : FunExtAt ℓ) (@♭ X : Set ℓ) (@♭ K : Closed X) where

    open Existence X K

    module Uniqueness (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

      open Target D D-set D-discrete

      -- The steps below are stated before the point z is bound, so that
      -- they are crisp.
      private
        pre : MapOver p q → MapOver (fst {B = A}) q
        pre = R.precomposeOver U A T p u uo D q

        lift : (T → D) → MapOver p q
        lift g = over-map g (λ z → from-end (p z))

        E = R.Output.universal K D D-discrete q q-set-fibers

        pointwise : (g g′ : T → D) → ((x : X) → g (η₀ x) ≡ g′ (η₀ x))
                  → (a : Σ U A) → g (u a) ≡ g′ (u a)
        pointwise g g′ e (end-at , raise x) = e x

        same : (@♭ g g′ : T → D) (@♭ e : (x : X) → g (η₀ x) ≡ g′ (η₀ x))
             → pre (lift g) ≡ pre (lift g′)
        same g g′ e = ap (λ h → over-map h (λ a → from-end (p (u a)) ∙ uo a))
          (fe (pointwise g g′ e))

        boxed : (@♭ g g′ : T → D) (@♭ e : (x : X) → g (η₀ x) ≡ g′ (η₀ x))
              → box (lift g) ≡ box (lift g′)
        boxed g g′ e = sym (retraction E (box (lift g)))
                     ∙ ap (inverse E) (box-crisp-path (same g g′ e))
                     ∙ retraction E (box (lift g′))

      unique₀ : (@♭ g g′ : T → D) (@♭ e : (x : X) → g (η₀ x) ≡ g′ (η₀ x))
              → (z : T) → g z ≡ g′ z
      unique₀ g g′ e z = ap (λ w → function (counit w) z) (boxed g g′ e)

    data-of : ShapeData X
    data-of = shape-data T T-set (R.Output.total-discrete K) η₀
      (λ D D-set D-discrete f → Target.rec₀ D D-set D-discrete f)
      (λ D D-set D-discrete f → Target.rec₀-η D D-set D-discrete f)
      (λ D D-set D-discrete g g′ e → Uniqueness.unique₀ D D-set D-discrete g g′ e)

  closed-bridge : (@♭ fe : FunExtAt ℓ) → ClosedBridge ℓ
  closed-bridge fe X K = Bridge.data-of fe X K
