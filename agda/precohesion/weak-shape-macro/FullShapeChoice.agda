{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Two full relative shapes of one diagram are equivalent over the base,
-- compatibly with their units; and so are their fibres.
-- Claude (Fable), 14 November 2026; fable-impl-23 (HANDOFF-38).
--
-- ShapeChoice.Choice and FiberChoice for the full interface. The maps
-- both ways are the factorisations of the two units; their composites are
-- identities AS WHOLE MAPS over the base, by FullOutput.unique. The
-- fibrewise inverse laws are read off those equalities of whole maps.
-- Where the Shape₀ proof closes with the sethood of the fibres, this one
-- uses Adjointify.quasi-inverse: the fibres of a full shape are not sets.
--
-- One hypothesis: crisp same-level function extensionality, used only in
-- the associativity law of composition of whole maps (ShapeChoice.Algebra).
module FullShapeChoice where

open import Foundations
open import RelativeSliceShape using (MapOver; over-map; function; triangle)
open import ShapeChoice
  using (FunExtAt; id-over; compose-over; module Algebra; fiber-map;
         fiber-map-id; fiber-map-compose)
open import Adjointify using (quasi-inverse)
open import FullRelativeShape

module Choice
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ}
  {@♭ A : Γ → Set ℓ}
  (@♭ fe : FunExtAt ℓ)
  (@♭ s t : FullShapeOver Γ dΓ A) where

  open Algebra fe

  unit-s : MapOver (fst {B = A}) (FullOutput.projection s)
  unit-s = over-map (FullOutput.unit s) (FullOutput.unit-over s)

  unit-t : MapOver (fst {B = A}) (FullOutput.projection t)
  unit-t = over-map (FullOutput.unit t) (FullOutput.unit-over t)

  forward-over : MapOver (FullOutput.projection s) (FullOutput.projection t)
  forward-over = FullOutput.factor s (FullOutput.Total t)
    (FullOutput.total-discrete t) (FullOutput.projection t) unit-t

  backward-over : MapOver (FullOutput.projection t) (FullOutput.projection s)
  backward-over = FullOutput.factor t (FullOutput.Total s)
    (FullOutput.total-discrete s) (FullOutput.projection s) unit-s

  forward-unit : compose-over forward-over unit-s ≡ unit-t
  forward-unit = FullOutput.factor-β s (FullOutput.Total t)
    (FullOutput.total-discrete t) (FullOutput.projection t) unit-t

  backward-unit : compose-over backward-over unit-t ≡ unit-s
  backward-unit = FullOutput.factor-β t (FullOutput.Total s)
    (FullOutput.total-discrete s) (FullOutput.projection s) unit-s

  forward-unique
    : (@♭ g : MapOver (FullOutput.projection s) (FullOutput.projection t))
    → (@♭ e : compose-over g unit-s ≡ unit-t)
    → g ≡ forward-over
  forward-unique g e = FullOutput.unique s (FullOutput.Total t)
    (FullOutput.total-discrete t) (FullOutput.projection t)
    g forward-over (e ∙ sym forward-unit)

  backward-forward-over : compose-over backward-over forward-over
                       ≡ id-over (FullOutput.projection s)
  backward-forward-over =
    FullOutput.unique s (FullOutput.Total s) (FullOutput.total-discrete s)
      (FullOutput.projection s)
      (compose-over backward-over forward-over)
      (id-over (FullOutput.projection s))
      (compose-assoc backward-over forward-over unit-s
       ∙ ap (compose-over backward-over) forward-unit
       ∙ backward-unit)

  forward-backward-over : compose-over forward-over backward-over
                       ≡ id-over (FullOutput.projection t)
  forward-backward-over =
    FullOutput.unique t (FullOutput.Total t) (FullOutput.total-discrete t)
      (FullOutput.projection t)
      (compose-over forward-over backward-over)
      (id-over (FullOutput.projection t))
      (compose-assoc forward-over backward-over unit-t
       ∙ ap (compose-over forward-over) backward-unit
       ∙ forward-unit)

  forward : FullOutput.Total s → FullOutput.Total t
  forward = function forward-over

  backward : FullOutput.Total t → FullOutput.Total s
  backward = function backward-over

  backward-forward : (x : FullOutput.Total s) → backward (forward x) ≡ x
  backward-forward x = ap (λ f → function f x) backward-forward-over

  forward-backward : (y : FullOutput.Total t) → forward (backward y) ≡ y
  forward-backward y = ap (λ f → function f y) forward-backward-over

  -- The carriers are equivalent. No sethood is used.
  forward-is-equiv : IsEquiv forward
  forward-is-equiv = quasi-inverse backward forward-backward backward-forward

  forward-on-unit : (a : Σ Γ A)
                  → forward (FullOutput.unit s a) ≡ FullOutput.unit t a
  forward-on-unit a = ap (λ f → function f a) forward-unit

  backward-on-unit : (a : Σ Γ A)
                   → backward (FullOutput.unit t a) ≡ FullOutput.unit s a
  backward-on-unit a = ap (λ f → function f a) backward-unit

module FiberChoice
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ}
  {@♭ A : Γ → Set ℓ}
  (@♭ fe : FunExtAt ℓ)
  (@♭ s t : FullShapeOver Γ dΓ A) where

  module C = Choice fe s t

  forward : (γ : Γ) → FullOutput.family s γ → FullOutput.family t γ
  forward = fiber-map C.forward-over

  backward : (γ : Γ) → FullOutput.family t γ → FullOutput.family s γ
  backward = fiber-map C.backward-over

  backward-forward : (γ : Γ) → (x : FullOutput.family s γ)
                   → backward γ (forward γ x) ≡ x
  backward-forward γ x = fiber-map-compose C.backward-over C.forward-over γ x
    ∙ ap (λ f → fiber-map f γ x) C.backward-forward-over
    ∙ fiber-map-id γ x

  forward-backward : (γ : Γ) → (y : FullOutput.family t γ)
                   → forward γ (backward γ y) ≡ y
  forward-backward γ y = fiber-map-compose C.forward-over C.backward-over γ y
    ∙ ap (λ f → fiber-map f γ y) C.forward-backward-over
    ∙ fiber-map-id γ y

  -- The fibres are equivalent: a quasi-inverse, improved by
  -- Adjointify. The Shape₀ proof uses the sethood of the fibre here.
  forward-is-equiv : (γ : Γ) → IsEquiv (forward γ)
  forward-is-equiv γ =
    quasi-inverse (backward γ) (forward-backward γ) (backward-forward γ)

  forward-on-unit : (γ : Γ) (a : A γ)
                  → forward γ (FullOutput.family-unit s γ a)
                    ≡ FullOutput.family-unit t γ a
  forward-on-unit γ a = ap
    (λ f → function f (γ , a) , triangle f (γ , a)) C.forward-unit
