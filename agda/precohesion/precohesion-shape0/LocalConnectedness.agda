{-# OPTIONS --safe --without-K --cohesion #-}

open import Foundations
import CandidateShape0
import FunctorLaws

module LocalConnectedness
  (@♭ Shape₀ : (@♭ A : Set) → Set)
  (@♭ unit₀ : (@♭ A : Set) → A → Shape₀ A)
  (@♭ shape-is-set : (@♭ A : Set) → IsSet (Shape₀ A))
  (@♭ shape-is-discrete : (@♭ A : Set) → Discrete (Shape₀ A))
  where

open CandidateShape0 Shape₀ unit₀ shape-is-set shape-is-discrete

Pullback : {A B C : Set} → (A → C) → (B → C) → Set
Pullback {A} {B} p f = Σ A (λ a → Σ B (λ b → p a ≡ f b))

left : {A B C : Set} {p : A → C} {f : B → C} → Pullback p f → A
left = fst

right : {A B C : Set} {p : A → C} {f : B → C} → Pullback p f → B
right x = fst (snd x)

commutes : {A B C : Set} {p : A → C} {f : B → C}
         → (x : Pullback p f) → p (left x) ≡ f (right x)
commutes x = snd (snd x)

module Target (@♭ universal : UniversalProperty)
              (@♭ fe : FunExt)
              (@♭ box-identity : BoxIdentity) where
  open Reflection universal
  open FunctorLaws Shape₀ unit₀ shape-is-set shape-is-discrete
    using (module Laws)
  open Laws universal fe box-identity

  module Comparison (@♭ A S T : Set)
                    (@♭ ss : IsSet S) (@♭ sd : Discrete S)
                    (@♭ ts : IsSet T) (@♭ td : Discrete T)
                    (@♭ p : A → S) (@♭ f : T → S) where

    P : Set
    P = Pullback p f

    p-bar : Shape₀ A → S
    p-bar = rec A S ss sd p

    t-bar : Shape₀ P → T
    t-bar = rec P T ts td right

    square-on-units : (x : P)
                    → p-bar (map left (unit₀ P x)) ≡ f (t-bar (unit₀ P x))
    square-on-units x =
      ap p-bar (map-unit left x)
      ∙ rec-β A S ss sd p (left x)
      ∙ commutes x
      ∙ sym (ap f (rec-β P T ts td right x))

    square : p-bar ∘ map left ≡ f ∘ t-bar
    square = unique P S ss sd (p-bar ∘ map left) (f ∘ t-bar) square-on-units

    pullback-comparison : Shape₀ P → Pullback p-bar f
    pullback-comparison z = map left z , t-bar z , happly square z

  -- This is a target proposition, not a parameter or postulate.
  SetLocalConnectedness : Set₁
  SetLocalConnectedness = (@♭ A S T : Set)
                       → (@♭ aset : IsSet A)
                       → (@♭ ss : IsSet S) → (@♭ sd : Discrete S)
                       → (@♭ ts : IsSet T) → (@♭ td : Discrete T)
                       → (@♭ p : A → S) → (@♭ f : T → S)
                       → IsEquiv (Comparison.pullback-comparison A S T ss sd ts td p f)
