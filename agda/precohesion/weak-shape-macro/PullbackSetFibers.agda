{-# OPTIONS --cohesion --without-K --flat-split #-}

module PullbackSetFibers where

open import Foundations
open import RelativeSliceShape using (SetFibers)

-- All the h-level arguments in this module are ordinary native type theory.
-- In particular, they use neither function extensionality nor new axioms.
transport : ∀ {a b} {A : Set a} (B : A → Set b)
          → {x y : A} → x ≡ y → B x → B y
transport B refl b = b

left-inverse : ∀ {a} {A : Set a} {x y : A}
             → (p : x ≡ y) → sym p ∙ p ≡ refl
left-inverse refl = refl

retract-set : ∀ {a b} {A : Set a} {B : Set b}
            → (f : A → B) (g : B → A)
            → ((x : A) → g (f x) ≡ x)
            → IsSet B → IsSet A
retract-set {A = A} f g h bs x y p q =
  sym (recover p)
  ∙ ap restore (bs (f x) (f y) (ap f p) (ap f q))
  ∙ recover q
  where
  restore : {x y : A} → f x ≡ f y → x ≡ y
  restore {x} {y} r = sym (h x) ∙ ap g r ∙ h y

  recover : {x y : A} → (r : x ≡ y) → restore (ap f r) ≡ r
  recover {x} refl = left-inverse (h x)

fiber-fst-out : ∀ {a b} {A : Set a} {B : A → Set b} {x : A}
              → Fiber (fst {B = B}) x → B x
fiber-fst-out {B = B} ((y , b) , p) = transport B p b

fiber-fst-in : ∀ {a b} {A : Set a} {B : A → Set b} {x : A}
             → B x → Fiber (fst {B = B}) x
fiber-fst-in {x = x} b = (x , b) , refl

fiber-fst-retraction : ∀ {a b} {A : Set a} {B : A → Set b} {x : A}
                     → (z : Fiber (fst {B = B}) x)
                     → fiber-fst-in (fiber-fst-out z) ≡ z
fiber-fst-retraction ((y , b) , refl) = refl

fiber-fst-set : ∀ {a b} {A : Set a} {B : A → Set b} (x : A)
              → IsSet (B x) → IsSet (Fiber (fst {B = B}) x)
fiber-fst-set x = retract-set fiber-fst-out fiber-fst-in fiber-fst-retraction

Pullback : ∀ {ℓ} {Γ Γ′ S : Set ℓ}
          → (p : S → Γ) → (f : Γ′ → Γ) → Set ℓ
Pullback {Γ′ = Γ′} p f = Σ Γ′ (λ γ′ → Fiber p (f γ′))

-- Reindexing a family with set fibers again has set fibers. No sethood
-- condition is imposed on either base or on the total space.
pullback-set-fibers : {@♭ ℓ : Level} {@♭ Γ Γ′ S : Set ℓ}
                    → (@♭ p : S → Γ) (@♭ f : Γ′ → Γ)
                    → SetFibers p
                    → SetFibers (fst {B = λ γ′ → Fiber p (f γ′)})
pullback-set-fibers p f pf γ′ = fiber-fst-set γ′ (pf (f γ′))
