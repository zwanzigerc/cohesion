{-# OPTIONS --safe --without-K --cohesion #-}

open import Foundations

-- A single-universe experiment. All assumptions are module parameters.
-- This is a candidate for weak shape, not a claim of semantic adequacy.
module CandidateShape0
  (@♭ Shape₀ : (@♭ A : Set) → Set)
  (@♭ unit₀ : (@♭ A : Set) → A → Shape₀ A)
  (@♭ shape-is-set : (@♭ A : Set) → IsSet (Shape₀ A))
  (@♭ shape-is-discrete : (@♭ A : Set) → Discrete (Shape₀ A))
  where

precompose : (@♭ A D : Set) → (Shape₀ A → D) → A → D
precompose A D g = g ∘ unit₀ A

flat-precompose : (@♭ A D : Set) → ♭ (Shape₀ A → D) → ♭ (A → D)
flat-precompose A D = flat-map (precompose A D)

UniversalProperty : Set₁
UniversalProperty = (@♭ A D : Set)
                  → (@♭ D-is-set : IsSet D)
                  → (@♭ D-is-discrete : Discrete D)
                  → IsEquiv (flat-precompose A D)

module Reflection (@♭ universal : UniversalProperty) where

  rec : (@♭ A D : Set)
      → (@♭ D-is-set : IsSet D)
      → (@♭ D-is-discrete : Discrete D)
      → (@♭ f : A → D) → Shape₀ A → D
  rec A D ds dd f = counit (inverse (universal A D ds dd) (box f))

  rec-β : (@♭ A D : Set)
        → (@♭ ds : IsSet D) → (@♭ dd : Discrete D)
        → (@♭ f : A → D) → (a : A)
        → rec A D ds dd f (unit₀ A a) ≡ f a
  rec-β A D ds dd f a = happly
    (sym (flat-map-counit (precompose A D)
      (inverse (universal A D ds dd) (box f)))
    ∙ ap counit (section (universal A D ds dd) (box f))) a

  rec-η : (@♭ A D : Set)
        → (@♭ ds : IsSet D) → (@♭ dd : Discrete D)
        → (@♭ g : Shape₀ A → D) → (z : Shape₀ A)
        → rec A D ds dd (g ∘ unit₀ A) z ≡ g z
  rec-η A D ds dd g z = happly
    (ap counit (retraction (universal A D ds dd) (box g))) z

  map : {@♭ A B : Set} → (@♭ f : A → B) → Shape₀ A → Shape₀ B
  map {A} {B} f = rec A (Shape₀ B)
    (shape-is-set B) (shape-is-discrete B) (unit₀ B ∘ f)

  map-unit : {@♭ A B : Set} → (@♭ f : A → B) → (a : A)
           → map f (unit₀ A a) ≡ unit₀ B (f a)
  map-unit {A} {B} f = rec-β A (Shape₀ B)
    (shape-is-set B) (shape-is-discrete B) (unit₀ B ∘ f)

  map-id : (@♭ A : Set) → (z : Shape₀ A) → map (id {A = A}) z ≡ z
  map-id A = rec-η A (Shape₀ A)
    (shape-is-set A) (shape-is-discrete A) id

  product-comparison : (@♭ A B : Set)
                     → Shape₀ (A × B) → Shape₀ A × Shape₀ B
  product-comparison A B z = map fst z , map snd z

  terminal-comparison : Shape₀ ⊤ → ⊤
  terminal-comparison _ = tt

  PreservesBinaryProducts : Set₁
  PreservesBinaryProducts = (@♭ A B : Set) → IsEquiv (product-comparison A B)

  PreservesTerminal : Set
  PreservesTerminal = IsEquiv terminal-comparison

  -- Construct the comparison via products and evaluation, avoiding an
  -- attempted application of `map` to evaluation at an ordinary variable.
  module Products (@♭ products : PreservesBinaryProducts) where

    product-inverse-unit : (@♭ A B : Set) → (a : A) → (b : B)
                         → inverse (products A B) (unit₀ A a , unit₀ B b)
                           ≡ unit₀ (A × B) (a , b)
    product-inverse-unit A B a b =
      ap (inverse (products A B))
        (sym (pair-path (map-unit fst (a , b)) (map-unit snd (a , b))))
      ∙ retraction (products A B) (unit₀ (A × B) (a , b))

    continuity-comparison : (@♭ A S : Set)
                          → Shape₀ (S → A) → S → Shape₀ A
    continuity-comparison A S z s =
      map (λ (p : (S → A) × S) → fst p (snd p))
        (inverse (products (S → A) S) (z , unit₀ S s))

    continuity-on-units : (@♭ A S : Set) → (f : S → A) → (s : S)
                        → continuity-comparison A S (unit₀ (S → A) f) s
                          ≡ unit₀ A (f s)
    continuity-on-units A S f s =
      ap (map (λ (p : (S → A) × S) → fst p (snd p)))
        (product-inverse-unit (S → A) S f s)
      ∙ map-unit (λ (p : (S → A) × S) → fst p (snd p)) (f , s)

    -- The first theorem experiment is the ordinary, set-level one.
    -- The comparison itself was defined on arbitrary source types above.
    SetContinuity : Set₁
    SetContinuity = (@♭ A S : Set)
                  → (@♭ A-is-set : IsSet A)
                  → (@♭ S-is-set : IsSet S)
                  → (@♭ S-is-discrete : Discrete S)
                  → IsEquiv (continuity-comparison A S)

  points-to-pieces : (@♭ A : Set) → ♭ A → Shape₀ A
  points-to-pieces A = unit₀ A ∘ counit

  module Truncation (@♭ pt : PropositionalTruncation) where
    open PropositionalTruncation pt

    -- This belongs to precohesion, not to the reflection data itself.
    -- The initial ordinary theorem only asks it for cohesive sets.
    SetNullstellensatz : Set₁
    SetNullstellensatz = (@♭ A : Set) → (@♭ A-is-set : IsSet A)
                       → (z : Shape₀ A) → ∥ Fiber (points-to-pieces A) z ∥
