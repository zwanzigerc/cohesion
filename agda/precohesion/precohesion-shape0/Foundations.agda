{-# OPTIONS --safe --without-K --cohesion #-}

module Foundations where

open import Agda.Primitive public using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Unit public

infixr 4 _×_
_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

id : ∀ {a} {A : Set a} → A → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
    → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

ap : ∀ {a b} {A : Set a} {B : Set b} (f : A → B)
   → {x y : A} → x ≡ y → f x ≡ f y
ap f refl = refl

sym : ∀ {a} {A : Set a} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

infixr 5 _∙_
_∙_ : ∀ {a} {A : Set a} {x y z : A}
    → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

happly : ∀ {a b} {A : Set a} {B : A → Set b}
       → {f g : (x : A) → B x} → f ≡ g → (x : A) → f x ≡ g x
happly refl x = refl

IsProp : ∀ {a} → Set a → Set a
IsProp A = (x y : A) → x ≡ y

IsSet : ∀ {a} → Set a → Set a
IsSet A = (x y : A) → IsProp (x ≡ y)

IsContr : ∀ {a} → Set a → Set a
IsContr A = Σ A (λ x → (y : A) → x ≡ y)

Fiber : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Set (a ⊔ b)
Fiber {A = A} f y = Σ A (λ x → f x ≡ y)

IsEquiv : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Set (a ⊔ b)
IsEquiv {B = B} f = (y : B) → IsContr (Fiber f y)

inverse : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
        → IsEquiv f → B → A
inverse e y = fst (fst (e y))

section : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
        → (e : IsEquiv f) → (y : B) → f (inverse e y) ≡ y
section e y = snd (fst (e y))

retraction : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
           → (e : IsEquiv f) → (x : A) → inverse e (f x) ≡ x
retraction {f = f} e x = ap fst (snd (e (f x)) (x , refl))

data ♭ {@♭ a : Level} (@♭ A : Set a) : Set a where
  box : (@♭ x : A) → ♭ A

counit : {@♭ a : Level} {@♭ A : Set a} → ♭ A → A
counit (box x) = x

flat-map : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
         → (@♭ f : A → B) → ♭ A → ♭ B
flat-map f (box x) = box (f x)

flat-map-counit : {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
                → (@♭ f : A → B) → (x : ♭ A)
                → counit (flat-map f x) ≡ f (counit x)
flat-map-counit f (box x) = refl

Discrete : {@♭ a : Level} (@♭ A : Set a) → Set a
Discrete A = IsEquiv (counit {A = A})

FunExt : Set₁
FunExt = {A : Set} {B : A → Set} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g

pair-path : ∀ {a b} {A : Set a} {B : Set b}
          → {x x' : A} {y y' : B}
          → x ≡ x' → y ≡ y' → (x , y) ≡ (x' , y')
pair-path refl refl = refl

BoxIdentity : Set₁
BoxIdentity = (@♭ A : Set) (@♭ x y : A)
            → (@♭ p : x ≡ y) → box x ≡ box y

record PropositionalTruncation : Set₁ where
  field
    ∥_∥ : Set → Set
    ∣_∣ : {A : Set} → A → ∥ A ∥
    trunc-is-prop : {A : Set} → IsProp (∥ A ∥)
    trunc-rec : {A P : Set} → IsProp P → (A → P) → ∥ A ∥ → P
