{-# OPTIONS --cohesion --without-K --flat-split #-}

module FlatContext where

open import Foundations

right-unit : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
right-unit refl = refl

fiber-path : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
           → {y : B} {x x' : A} {p : f x ≡ y} {p' : f x' ≡ y}
           → (q : x ≡ x') → ap f q ∙ p' ≡ p
           → (x , p) ≡ (x' , p')
fiber-path {x = x} refl h = ap (λ p → x , p) (sym h)

-- A coherent inverse gives contractible fibers, without any sethood axiom.
coherent-inverse : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
                 → (g : B → A)
                 → (sec : (y : B) → f (g y) ≡ y)
                 → (ret : (x : A) → g (f x) ≡ x)
                 → ((x : A) → ap f (ret x) ≡ sec (f x))
                 → IsEquiv f
coherent-inverse {A = A} {B = B} {f = f} g sec ret triangle y =
  (g y , sec y) , λ { (x , p) → contraction x y p }
  where
  contraction : (x : A) (y : B) (p : f x ≡ y)
              → (g y , sec y) ≡ (x , p)
  contraction x .(f x) refl =
    fiber-path (ret x) (right-unit (ap f (ret x)) ∙ triangle x)

duplicate : {@♭ a : Level} {@♭ A : Set a} → ♭ A → ♭ (♭ A)
duplicate (box x) = box (box x)

duplicate-section : {@♭ a : Level} {@♭ A : Set a}
                  → (y : ♭ A) → counit (duplicate y) ≡ y
duplicate-section (box x) = refl

duplicate-retraction : {@♭ a : Level} {@♭ A : Set a}
                     → (x : ♭ (♭ A)) → duplicate (counit x) ≡ x
duplicate-retraction (box (box x)) = refl

duplicate-triangle : {@♭ a : Level} {@♭ A : Set a}
                   → (x : ♭ (♭ A))
                   → ap counit (duplicate-retraction x)
                     ≡ duplicate-section (counit x)
duplicate-triangle (box (box x)) = refl

flat-discrete : {@♭ a : Level} (@♭ A : Set a) → Discrete (♭ A)
flat-discrete A = coherent-inverse duplicate duplicate-section
  duplicate-retraction duplicate-triangle

-- The crisp context A : Set is represented by the native type ♭ Set.
-- It need not be a homotopical set. No universe-sethood axiom is introduced.
TypeContext : Set₁
TypeContext = ♭ Set

type-context-discrete : Discrete TypeContext
type-context-discrete = flat-discrete Set

data Lift (A : Set) : Set₁ where
  lift : A → Lift A

TypeFamily : TypeContext → Set₁
TypeFamily (box A) = Lift A
