{-# OPTIONS --cohesion --without-K --flat-split #-}

module DiscretePullback where

open import Foundations
open import FlatContext using (coherent-inverse; right-unit)
open import PullbackSetFibers using (Pullback) public

transport : ∀ {a b} {A : Set a} (P : A → Set b)
          → {x y : A} → x ≡ y → P x → P y
transport P refl px = px

-- For the idempotent flat comonad, a crisp section of its counit suffices.
crisp-lift : {@♭ a : Level} {@♭ A : Set a}
            → (@♭ u : ♭ A) (@♭ x : A) (@♭ p : counit u ≡ x)
            → Σ (u ≡ box x) (λ q → ap counit q ≡ p)
crisp-lift (box x) .x refl = refl , refl

counit-section-discrete : {@♭ a : Level} {@♭ A : Set a}
                        → (@♭ lift : A → ♭ A)
                        → (@♭ sec : (x : A) → counit (lift x) ≡ x)
                        → Discrete A
counit-section-discrete lift sec = coherent-inverse lift sec ret triangle
  where
  ret : (u : ♭ _) → lift (counit u) ≡ u
  ret (box x) = fst (crisp-lift (lift x) x (sec x))

  triangle : (u : ♭ _) → ap counit (ret u) ≡ sec (counit u)
  triangle (box x) = snd (crisp-lift (lift x) x (sec x))

-- A discrete type admits dependent elimination from crisp representatives.
discrete-ind : {@♭ a : Level} {b : Level} {@♭ A : Set a}
             → (@♭ da : Discrete A) → (P : A → Set b)
             → ((@♭ x : A) → P x) → (x : A) → P x
discrete-ind da P k x = transport P (section da x) (on-flat (inverse da x))
  where
  on-flat : (u : ♭ _) → P (counit u)
  on-flat (box y) = k y

-- Native identity in a flat type can be encoded by a flat native identity.
Code : {@♭ a : Level} {@♭ A : Set a} → ♭ A → ♭ A → Set a
Code (box x) (box y) = ♭ (x ≡ y)

code-refl : {@♭ a : Level} {@♭ A : Set a} → (u : ♭ A) → Code u u
code-refl (box x) = box refl

path-to-code : {@♭ a : Level} {@♭ A : Set a}
             → (u v : ♭ A) → u ≡ v → Code u v
path-to-code u .u refl = code-refl u

code-counit : {@♭ a : Level} {@♭ A : Set a}
            → (u v : ♭ A) → Code u v → counit u ≡ counit v
code-counit (box x) (box y) = counit

code-counit-path : {@♭ a : Level} {@♭ A : Set a}
                 → (u v : ♭ A) (q : u ≡ v)
                 → code-counit u v (path-to-code u v q) ≡ ap counit q
code-counit-path (box x) .(box x) refl = refl

fiber-path-first : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
                 → {y : B} {x x' : A} {p : f x ≡ y} {p' : f x' ≡ y}
                 → (h : (x , p) ≡ (x' , p'))
                 → ap f (ap fst h) ∙ p' ≡ p
fiber-path-first refl = refl

module Identity
  {@♭ a : Level} {@♭ A : Set a} (@♭ da : Discrete A)
  (@♭ x y : A) where

  fiber-path-between : (p : x ≡ y)
                     → (box x , p) ≡ (box y , refl)
  fiber-path-between p =
    sym (snd (da y) (box x , p)) ∙ snd (da y) (box y , refl)

  lifted-path : (p : x ≡ y) → box x ≡ box y
  lifted-path p = ap fst (fiber-path-between p)

  lifted-path-section : (p : x ≡ y) → ap counit (lifted-path p) ≡ p
  lifted-path-section p =
    sym (right-unit (ap counit (lifted-path p)))
    ∙ fiber-path-first (fiber-path-between p)

  lift : (x ≡ y) → ♭ (x ≡ y)
  lift p = path-to-code (box x) (box y) (lifted-path p)

  lift-section : (p : x ≡ y) → counit (lift p) ≡ p
  lift-section p = code-counit-path (box x) (box y) (lifted-path p)
    ∙ lifted-path-section p

  discrete : Discrete (x ≡ y)
  discrete = counit-section-discrete lift lift-section

identity-discrete : {@♭ a : Level} {@♭ A : Set a}
                  → (@♭ da : Discrete A) (@♭ x y : A) → Discrete (x ≡ y)
identity-discrete = Identity.discrete

module PullbackDiscrete
  {@♭ ℓ : Level} {@♭ Γ Γ′ S : Set ℓ}
  (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′) (@♭ dS : Discrete S)
  (@♭ p : S → Γ) (@♭ f : Γ′ → Γ) where

  LiftFiber : Pullback p f → Set ℓ
  LiftFiber = Fiber (counit {A = Pullback p f})

  has-lift-at-path : (@♭ γ′ : Γ′) (@♭ s : S)
                   → (e : p s ≡ f γ′)
                   → LiftFiber (γ′ , s , e)
  has-lift-at-path γ′ s = discrete-ind (identity-discrete dΓ (p s) (f γ′))
    (λ e → LiftFiber (γ′ , s , e)) (λ e → box (γ′ , s , e) , refl)

  has-lift-at-point : (@♭ γ′ : Γ′) → (s : S) → (e : p s ≡ f γ′)
                    → LiftFiber (γ′ , s , e)
  has-lift-at-point γ′ = discrete-ind dS
    (λ s → (e : p s ≡ f γ′) → LiftFiber (γ′ , s , e))
    (has-lift-at-path γ′)

  has-lift-at-base : (γ′ : Γ′) → (s : S) → (e : p s ≡ f γ′)
                   → LiftFiber (γ′ , s , e)
  has-lift-at-base = discrete-ind dΓ′
    (λ γ′ → (s : S) → (e : p s ≡ f γ′) → LiftFiber (γ′ , s , e))
    has-lift-at-point

  has-lift : (z : Pullback p f) → LiftFiber z
  has-lift (γ′ , s , e) = has-lift-at-base γ′ s e

  lift : Pullback p f → ♭ (Pullback p f)
  lift z = fst (has-lift z)

  lift-section : (z : Pullback p f) → counit (lift z) ≡ z
  lift-section z = snd (has-lift z)

  discrete : Discrete (Pullback p f)
  discrete = counit-section-discrete lift lift-section

pullback-discrete : {@♭ ℓ : Level} {@♭ Γ Γ′ S : Set ℓ}
                  → (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
                  → (@♭ dS : Discrete S)
                  → (@♭ p : S → Γ) (@♭ f : Γ′ → Γ)
                  → Discrete (Pullback p f)
pullback-discrete = PullbackDiscrete.discrete
