{-# OPTIONS --without-K --cohesion --flat-split #-}

open import Foundations
import CandidateShape0
import FunctorLaws

-- A negative-strength probe: no continuity or product-preservation hypothesis.
-- Crisp splitting is used to establish closure of discrete sets under sums.
module StabilityProbe
  (@♭ Shape₀ : (@♭ A : Set) → Set)
  (@♭ unit₀ : (@♭ A : Set) → A → Shape₀ A)
  (@♭ shape-is-set : (@♭ A : Set) → IsSet (Shape₀ A))
  (@♭ shape-is-discrete : (@♭ A : Set) → Discrete (Shape₀ A))
  where

open CandidateShape0 Shape₀ unit₀ shape-is-set shape-is-discrete

transport : {A : Set} (B : A → Set) {x y : A} → x ≡ y → B x → B y
transport B refl u = u

sigma-path : {A : Set} {B : A → Set} {x y : A} {u : B x} {v : B y}
           → (p : x ≡ y) → transport B p u ≡ v → (x , u) ≡ (y , v)
sigma-path refl refl = refl

sigma-prop : {A : Set} {B : A → Set}
           → IsProp A → ((x : A) → IsProp (B x)) → IsProp (Σ A B)
sigma-prop ap bp (x , u) (y , v) = sigma-path (ap x y)
  (bp y (transport _ (ap x y) u) v)

PathCode : {A : Set} {B : A → Set} → Σ A B → Σ A B → Set
PathCode {B = B} (x , u) (y , v) = Σ (x ≡ y) (λ p → transport B p u ≡ v)

encode : {A : Set} {B : A → Set} {s t : Σ A B} → s ≡ t → PathCode s t
encode refl = refl , refl

decode : {A : Set} {B : A → Set} {s t : Σ A B} → PathCode s t → s ≡ t
decode (p , q) = sigma-path p q

decode-encode : {A : Set} {B : A → Set} {s t : Σ A B}
              → (p : s ≡ t) → decode (encode p) ≡ p
decode-encode refl = refl

sigma-set : {A : Set} {B : A → Set}
          → IsSet A → ((x : A) → IsSet (B x)) → IsSet (Σ A B)
sigma-set {B = B} as bs s@(x , u) t@(y , v) p q =
  sym (decode-encode p)
  ∙ ap decode (sigma-prop (as x y)
      (λ r → bs y (transport B r u) v) (encode p) (encode q))
  ∙ decode-encode q

left-inverse : {A : Set} {x y : A} → (p : x ≡ y) → sym p ∙ p ≡ refl
left-inverse refl = refl

retract-set : {A B : Set} (f : A → B) (g : B → A)
            → ((x : A) → g (f x) ≡ x) → IsSet B → IsSet A
retract-set {A} f g h bs x y p q =
  sym (recover p) ∙ ap restore (bs (f x) (f y) (ap f p) (ap f q)) ∙ recover q
  where
  restore : {x y : A} → f x ≡ f y → x ≡ y
  restore {x} {y} r = sym (h x) ∙ ap g r ∙ h y

  recover : {x y : A} → (r : x ≡ y) → restore (ap f r) ≡ r
  recover {x} refl = left-inverse (h x)

set-qinv : {A B : Set} {f : A → B} → IsSet B → (g : B → A)
         → ((y : B) → f (g y) ≡ y) → ((x : A) → g (f x) ≡ x)
         → IsEquiv f
set-qinv {f = f} bs g sec ret y = (g y , sec y) , λ (x , p) →
  sigma-path (ap g (sym p) ∙ ret x)
    (bs (f x) y (transport (λ a → f a ≡ y) (ap g (sym p) ∙ ret x) (sec y)) p)

module Probe (@♭ universal : UniversalProperty)
             (@♭ fe : FunExt)
             (@♭ box-identity : BoxIdentity) where

  open Reflection universal
  open FunctorLaws.Laws Shape₀ unit₀ shape-is-set shape-is-discrete
    universal fe box-identity

  -- Using flat indices makes the crispness of each family member explicit.
  -- For a discrete I, its flat counit identifies these indices with I itself.
  module Family (@♭ I : Set) (@♭ is : IsSet I) (@♭ di : Discrete I)
                (@♭ A : I → Set) where

    F : ♭ I → Set
    F (box i) = A i

    SF : ♭ I → Set
    SF (box i) = Shape₀ (A i)

    Total : Set
    Total = Σ (♭ I) F

    ShapedTotal : Set
    ShapedTotal = Σ (♭ I) SF

    flat-index-set : IsSet (♭ I)
    flat-index-set = retract-set counit (inverse di) (retraction di) is

    shaped-total-set : IsSet ShapedTotal
    shaped-total-set = sigma-set flat-index-set λ { (box i) → shape-is-set (A i) }

    box-insert : (@♭ i : I) → ♭ (Shape₀ (A i)) → ♭ ShapedTotal
    box-insert i (box z) = box (box i , z)

    box-insert-counit : (@♭ i : I) → (z : ♭ (Shape₀ (A i)))
                      → counit (box-insert i z) ≡ (box i , counit z)
    box-insert-counit i (box z) = refl

    shaped-total-lift : ShapedTotal → ♭ ShapedTotal
    shaped-total-lift (box i , z) = box-insert i (inverse (shape-is-discrete (A i)) z)

    shaped-total-section : (y : ShapedTotal) → counit (shaped-total-lift y) ≡ y
    shaped-total-section (box i , z) =
      box-insert-counit i (inverse (shape-is-discrete (A i)) z)
      ∙ ap (λ w → box i , w) (section (shape-is-discrete (A i)) z)

    shaped-total-retraction : (y : ♭ ShapedTotal) → shaped-total-lift (counit y) ≡ y
    shaped-total-retraction (box (box i , z)) =
      ap (box-insert i) (retraction (shape-is-discrete (A i)) (box z))

    shaped-total-discrete : Discrete ShapedTotal
    shaped-total-discrete = set-qinv shaped-total-set shaped-total-lift
      shaped-total-section shaped-total-retraction

    insert : (@♭ i : I) → A i → Total
    insert i a = box i , a

    total-unit : Total → ShapedTotal
    total-unit (box i , a) = box i , unit₀ (A i) a

    forward : Shape₀ Total → ShapedTotal
    forward = rec Total ShapedTotal shaped-total-set shaped-total-discrete total-unit

    backward : ShapedTotal → Shape₀ Total
    backward (box i , z) = map (insert i) z

    forward-backward : (y : ShapedTotal) → forward (backward y) ≡ y
    forward-backward (box i , z) = happly
      (unique (A i) ShapedTotal shaped-total-set shaped-total-discrete
        (forward ∘ map (insert i)) (λ w → box i , w)
        (λ a → ap forward (map-unit (insert i) a)
          ∙ rec-β Total ShapedTotal shaped-total-set shaped-total-discrete total-unit (box i , a))) z

    backward-forward : (z : Shape₀ Total) → backward (forward z) ≡ z
    backward-forward = happly
      (unique Total (Shape₀ Total) (shape-is-set Total) (shape-is-discrete Total)
        (backward ∘ forward) id
        (λ { (box i , a) →
          ap backward (rec-β Total ShapedTotal shaped-total-set shaped-total-discrete total-unit (box i , a))
          ∙ map-unit (insert i) a }))

    -- Discrete-set indexed sums commute with the candidate shape already
    -- under reflection, function extensionality, and crisp identity congruence.
    shape-sum-is-equiv : IsEquiv forward
    shape-sum-is-equiv = set-qinv shaped-total-set backward forward-backward backward-forward

    -- This checks a familywise shape/sum equivalence. Converting its result to
    -- the exact pullback comparison in LocalConnectedness.agda is not done
    -- here, and this experiment does not establish a semantics for the axioms.
