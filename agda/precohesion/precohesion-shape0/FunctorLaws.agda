{-# OPTIONS --safe --without-K --cohesion #-}

open import Foundations
import CandidateShape0

module FunctorLaws
  (@♭ Shape₀ : (@♭ A : Set) → Set)
  (@♭ unit₀ : (@♭ A : Set) → A → Shape₀ A)
  (@♭ shape-is-set : (@♭ A : Set) → IsSet (Shape₀ A))
  (@♭ shape-is-discrete : (@♭ A : Set) → Discrete (Shape₀ A))
  where

open CandidateShape0 Shape₀ unit₀ shape-is-set shape-is-discrete

module Laws (@♭ universal : UniversalProperty)
            (@♭ fe : FunExt)
            (@♭ box-identity : BoxIdentity) where
  open Reflection universal

  unique : (@♭ A D : Set)
         → (@♭ ds : IsSet D) → (@♭ dd : Discrete D)
         → (@♭ g h : Shape₀ A → D)
         → (@♭ on-units : (a : A) → g (unit₀ A a) ≡ h (unit₀ A a))
         → g ≡ h
  unique A D ds dd g h on-units =
    sym (ap counit (retraction (universal A D ds dd) (box g)))
    ∙ ap (counit ∘ inverse (universal A D ds dd))
        (box-identity (A → D) (g ∘ unit₀ A) (h ∘ unit₀ A) (fe on-units))
    ∙ ap counit (retraction (universal A D ds dd) (box h))

  map-composition : {@♭ A B C : Set} (@♭ f : A → B) (@♭ g : B → C)
                  → map (g ∘ f) ≡ (map g ∘ map f)
  map-composition {A} {B} {C} f g =
    unique A (Shape₀ C) (shape-is-set C) (shape-is-discrete C)
      (map (g ∘ f)) (map g ∘ map f)
      (λ a → map-unit (g ∘ f) a
        ∙ sym (ap (map g) (map-unit f a) ∙ map-unit g (f a)))

  discrete-retract : (@♭ D : Set) → (@♭ ds : IsSet D) → (@♭ dd : Discrete D)
                   → Shape₀ D → D
  discrete-retract D ds dd = rec D D ds dd id

  discrete-retract-unit : (@♭ D : Set)
                        → (@♭ ds : IsSet D) → (@♭ dd : Discrete D)
                        → (d : D) → discrete-retract D ds dd (unit₀ D d) ≡ d
  discrete-retract-unit D ds dd = rec-β D D ds dd id

  discrete-unit-retract : (@♭ D : Set)
                        → (@♭ ds : IsSet D) → (@♭ dd : Discrete D)
                        → (z : Shape₀ D) → unit₀ D (discrete-retract D ds dd z) ≡ z
  discrete-unit-retract D ds dd = happly
    (unique D (Shape₀ D) (shape-is-set D) (shape-is-discrete D)
      (unit₀ D ∘ discrete-retract D ds dd) id
      (λ d → ap (unit₀ D) (discrete-retract-unit D ds dd d)))
