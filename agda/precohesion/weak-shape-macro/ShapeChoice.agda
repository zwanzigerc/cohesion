{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Choice independence for two reflections of the SAME whole-context input.
-- Function extensionality is an explicit hypothesis; no axiom is declared.
module ShapeChoice where

open import Foundations
open import RelativeSliceShape
open import NativeSharp using (box-crisp-path)
open import FlatContext using (coherent-inverse; right-unit)

FunExtAt : (ℓ : Level) → Set (lsuc ℓ)
FunExtAt ℓ = {X : Set ℓ} {Y : X → Set ℓ}
           → {f g : (x : X) → Y x}
           → ((x : X) → f x ≡ g x) → f ≡ g

transport : ∀ {a b} {X : Set a} (Y : X → Set b)
          → {x y : X} → x ≡ y → Y x → Y y
transport Y refl z = z

assoc : ∀ {a} {X : Set a} {w x y z : X}
      → (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
      → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
assoc refl q r = refl

id-over : ∀ {ℓ} {Γ X : Set ℓ} (p : X → Γ) → MapOver p p
id-over p = over-map id (λ _ → refl)

compose-over : ∀ {ℓ} {Γ X Y Z : Set ℓ}
             → {p : X → Γ} {q : Y → Γ} {r : Z → Γ}
             → MapOver q r → MapOver p q → MapOver p r
compose-over g f = over-map (function g ∘ function f)
  (λ x → triangle g (function f x) ∙ triangle f x)

module Algebra {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) where

  compose-assoc : {Γ X Y Z W : Set ℓ}
                → {p : X → Γ} {q : Y → Γ} {r : Z → Γ} {s : W → Γ}
                → (h : MapOver r s) (g : MapOver q r) (f : MapOver p q)
                → compose-over (compose-over h g) f
                  ≡ compose-over h (compose-over g f)
  compose-assoc h g f = ap (over-map (function h ∘ function g ∘ function f))
    (fe (λ x → assoc (triangle h (function g (function f x)))
                      (triangle g (function f x)) (triangle f x)))

  compose-right-unit : {Γ X Y : Set ℓ} {p : X → Γ} {q : Y → Γ}
                     → (f : MapOver p q) → compose-over f (id-over p) ≡ f
  compose-right-unit f = ap (over-map (function f))
    (fe (λ x → right-unit (triangle f x)))

  compose-left-unit : {Γ X Y : Set ℓ} {p : X → Γ} {q : Y → Γ}
                    → (f : MapOver p q) → compose-over (id-over q) f ≡ f
  compose-left-unit f = refl

module Uniqueness
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ}
  {@♭ A : Γ → Set ℓ}
  (@♭ s : RelativeShapeOver Γ dΓ A)
  (@♭ D : Set ℓ) (@♭ dd : Discrete D)
  (@♭ q : D → Γ) (@♭ qf : SetFibers q) where

  pre : MapOver (Output.projection s) q → MapOver (fst {B = A}) q
  pre = precomposeOver Γ A (Output.Total s) (Output.projection s)
    (Output.unit s) (Output.unit-over s) D q

  factor-η : (@♭ g : MapOver (Output.projection s) q)
           → Output.factor s D dd q qf (pre g) ≡ g
  factor-η g = ap counit (retraction (Output.universal s D dd q qf) (box g))

  unique : (@♭ g h : MapOver (Output.projection s) q)
         → (@♭ e : pre g ≡ pre h) → g ≡ h
  unique g h e =
    sym (factor-η g)
    ∙ ap (λ z → counit (inverse (Output.universal s D dd q qf) z))
        (box-crisp-path e)
    ∙ factor-η h

module Choice
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ}
  {@♭ A : Γ → Set ℓ}
  (@♭ fe : FunExtAt ℓ)
  (@♭ s t : RelativeShapeOver Γ dΓ A) where

  open Algebra fe

  unit-s : MapOver (fst {B = A}) (Output.projection s)
  unit-s = over-map (Output.unit s) (Output.unit-over s)

  unit-t : MapOver (fst {B = A}) (Output.projection t)
  unit-t = over-map (Output.unit t) (Output.unit-over t)

  forward-over : MapOver (Output.projection s) (Output.projection t)
  forward-over = Output.factor s (Output.Total t) (Output.total-discrete t)
    (Output.projection t) (Output.family-set t) unit-t

  backward-over : MapOver (Output.projection t) (Output.projection s)
  backward-over = Output.factor t (Output.Total s) (Output.total-discrete s)
    (Output.projection s) (Output.family-set s) unit-s

  forward-unit : compose-over forward-over unit-s ≡ unit-t
  forward-unit = Output.factor-β s (Output.Total t) (Output.total-discrete t)
    (Output.projection t) (Output.family-set t) unit-t

  backward-unit : compose-over backward-over unit-t ≡ unit-s
  backward-unit = Output.factor-β t (Output.Total s) (Output.total-discrete s)
    (Output.projection s) (Output.family-set s) unit-s

  forward-unique : (@♭ g : MapOver (Output.projection s) (Output.projection t))
                 → (@♭ e : compose-over g unit-s ≡ unit-t)
                 → g ≡ forward-over
  forward-unique g e = Uniqueness.unique s (Output.Total t)
    (Output.total-discrete t) (Output.projection t) (Output.family-set t)
    g forward-over (e ∙ sym forward-unit)

  backward-forward-over : compose-over backward-over forward-over
                       ≡ id-over (Output.projection s)
  backward-forward-over =
    Uniqueness.unique s (Output.Total s) (Output.total-discrete s)
      (Output.projection s) (Output.family-set s)
      (compose-over backward-over forward-over) (id-over (Output.projection s))
      (compose-assoc backward-over forward-over unit-s
       ∙ ap (compose-over backward-over) forward-unit
       ∙ backward-unit)

  forward-backward-over : compose-over forward-over backward-over
                       ≡ id-over (Output.projection t)
  forward-backward-over =
    Uniqueness.unique t (Output.Total t) (Output.total-discrete t)
      (Output.projection t) (Output.family-set t)
      (compose-over forward-over backward-over) (id-over (Output.projection t))
      (compose-assoc forward-over backward-over unit-t
       ∙ ap (compose-over forward-over) backward-unit
       ∙ forward-unit)

  forward : Output.Total s → Output.Total t
  forward = function forward-over

  backward : Output.Total t → Output.Total s
  backward = function backward-over

  backward-forward : (x : Output.Total s) → backward (forward x) ≡ x
  backward-forward x = ap (λ f → function f x) backward-forward-over

  forward-backward : (y : Output.Total t) → forward (backward y) ≡ y
  forward-backward y = ap (λ f → function f y) forward-backward-over

  forward-on-unit : (a : Σ Γ A) → forward (Output.unit s a) ≡ Output.unit t a
  forward-on-unit a = ap (λ f → function f a) forward-unit

  backward-on-unit : (a : Σ Γ A) → backward (Output.unit t a) ≡ Output.unit s a
  backward-on-unit a = ap (λ f → function f a) backward-unit

-- Every map over a base induces a map on its native fibers.
fiber-map : ∀ {ℓ} {Γ X Y : Set ℓ} {p : X → Γ} {q : Y → Γ}
          → MapOver p q → (γ : Γ) → Fiber p γ → Fiber q γ
fiber-map f γ (x , e) = function f x , triangle f x ∙ e

fiber-map-id : ∀ {ℓ} {Γ X : Set ℓ} {p : X → Γ}
             → (γ : Γ) → (x : Fiber p γ) → fiber-map (id-over p) γ x ≡ x
fiber-map-id γ (x , e) = refl

fiber-map-compose : ∀ {ℓ} {Γ X Y Z : Set ℓ}
                  → {p : X → Γ} {q : Y → Γ} {r : Z → Γ}
                  → (g : MapOver q r) (f : MapOver p q)
                  → (γ : Γ) → (x : Fiber p γ)
                  → fiber-map g γ (fiber-map f γ x)
                    ≡ fiber-map (compose-over g f) γ x
fiber-map-compose g f γ (x , e) = ap (λ path → function g (function f x) , path)
  (sym (assoc (triangle g (function f x)) (triangle f x) e))

module FiberChoice
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ}
  {@♭ A : Γ → Set ℓ}
  (@♭ fe : FunExtAt ℓ)
  (@♭ s t : RelativeShapeOver Γ dΓ A) where

  module C = Choice fe s t

  forward : (γ : Γ) → Output.family s γ → Output.family t γ
  forward = fiber-map C.forward-over

  backward : (γ : Γ) → Output.family t γ → Output.family s γ
  backward = fiber-map C.backward-over

  backward-forward : (γ : Γ) → (x : Output.family s γ)
                   → backward γ (forward γ x) ≡ x
  backward-forward γ x = fiber-map-compose C.backward-over C.forward-over γ x
    ∙ ap (λ f → fiber-map f γ x) C.backward-forward-over
    ∙ fiber-map-id γ x

  forward-backward : (γ : Γ) → (y : Output.family t γ)
                   → forward γ (backward γ y) ≡ y
  forward-backward γ y = fiber-map-compose C.forward-over C.backward-over γ y
    ∙ ap (λ f → fiber-map f γ y) C.forward-backward-over
    ∙ fiber-map-id γ y

  forward-is-equiv : (γ : Γ) → IsEquiv (forward γ)
  forward-is-equiv γ = coherent-inverse (backward γ)
    (forward-backward γ) (backward-forward γ)
    (λ x → Output.family-set t γ _ _ _ _)

  forward-on-unit : (γ : Γ) (a : A γ)
                  → forward γ (Output.family-unit s γ a)
                    ≡ Output.family-unit t γ a
  forward-on-unit γ a = ap
    (λ f → function f (γ , a) , triangle f (γ , a)) C.forward-unit

  backward-on-unit : (γ : Γ) (a : A γ)
                   → backward γ (Output.family-unit t γ a)
                     ≡ Output.family-unit s γ a
  backward-on-unit γ a = ap
    (λ f → function f (γ , a) , triangle f (γ , a)) C.backward-unit
