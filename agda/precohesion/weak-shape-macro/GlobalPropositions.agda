{-# OPTIONS --cohesion --without-K --flat-split #-}

-- What it takes to call the witnesses of the global axioms propositions.
-- Postulate-free. Claude (Fable), 13 November 2026; fable-impl-02,
-- HANDOFF-04 items (a) and (g).
--
-- Merely A = (P : Set ℓ) → IsProp P → (A → P) → P   lives in Set (lsuc ℓ).
-- It has introduction, and elimination into propositions OF LEVEL ℓ ONLY.
-- Nothing here resizes it, and nothing eliminates it into a larger type.
--
--   merely-is-prop    needs extensionality for functions out of Set ℓ
--                     (FunExt₂ (lsuc ℓ) ℓ) and for functions between types
--                     of level ℓ (FunExt₂ ℓ ℓ).
--   to-truncation,    for any propositional truncation at level ℓ given as a
--   from-truncation   structure with its recursor: Merely A and ∥ A ∥ are
--                     logically equivalent with no extensionality, and
--                     equivalent types once both are propositions.
--   nullstellensatz-is-prop   needs in addition FunExt₂ ℓ (lsuc ℓ).
--   product-is-prop   IsEquiv of the comparison: FunExt₂ ℓ ℓ.
--
-- Without these hypotheses the witness types are still usable: every
-- consumer in GlobalPrecohesion and GlobalChoice works pointwise.
module GlobalPropositions where

open import Foundations
open import GlobalPrecohesion

FunExt₂ : (a b : Level) → Set (lsuc (a ⊔ b))
FunExt₂ a b = {X : Set a} {Y : X → Set b} {f g : (x : X) → Y x}
            → ((x : X) → f x ≡ g x) → f ≡ g

-- A propositional truncation at one level, as a structure.
record Truncation (ℓ : Level) : Set (lsuc ℓ) where
  field
    ∥_∥ : Set ℓ → Set ℓ
    ∣_∣ : {A : Set ℓ} → A → ∥ A ∥
    squash : {A : Set ℓ} → IsProp ∥ A ∥
    ∥-rec : {A P : Set ℓ} → IsProp P → (A → P) → ∥ A ∥ → P

module _ {@♭ ℓ : Level} where

  merely-intro : {A : Set ℓ} → A → Merely A
  merely-intro a P P-prop k = k a

  merely-map : {A B : Set ℓ} → (A → B) → Merely A → Merely B
  merely-map f m P P-prop k = m P P-prop (λ a → k (f a))

  merely-is-prop : FunExt₂ (lsuc ℓ) ℓ → FunExt₂ ℓ ℓ
                 → {A : Set ℓ} → IsProp (Merely A)
  merely-is-prop fe₁ fe₀ m m′ =
    fe₁ (λ P → fe₀ (λ P-prop → fe₀ (λ k → P-prop (m P P-prop k) (m′ P P-prop k))))

  module _ (t : Truncation ℓ) where
    open Truncation t

    to-truncation : {A : Set ℓ} → Merely A → ∥ A ∥
    to-truncation {A} m = m ∥ A ∥ squash ∣_∣

    from-truncation : {A : Set ℓ} → ∥ A ∥ → Merely A
    from-truncation x P P-prop k = ∥-rec P-prop k x

  nullstellensatz-is-prop :
    FunExt₂ (lsuc ℓ) ℓ → FunExt₂ ℓ ℓ → FunExt₂ ℓ (lsuc ℓ)
    → {@♭ X : Set ℓ} (@♭ s : ShapeData X) → IsProp (Nullstellensatz s)
  nullstellensatz-is-prop fe₁ fe₀ fe₂ s n n′ =
    fe₂ (λ z → merely-is-prop fe₁ fe₀ (n z) (n′ z))

------------------------------------------------------------------------
-- IsEquiv f is a proposition, for any f between types of one level.

private
  prop-set : ∀ {a} {A : Set a} → IsProp A → IsSet A
  prop-set {A = A} h x y u w = lemma u ∙ sym (lemma w)
    where
    cancel : {m n : A} (e : m ≡ n) → sym e ∙ e ≡ refl
    cancel refl = refl

    lemma : {z : A} (r : x ≡ z) → r ≡ sym (h x x) ∙ h x z
    lemma refl = sym (cancel (h x x))

contr-is-prop : ∀ {a} → FunExt₂ a a → {A : Set a} → IsProp (IsContr A)
contr-is-prop fe {A} (c , h) (c′ , h′) = lemma (h c′) h h′
  where
  -- A contractible type is a proposition, hence a set.
  A-set : IsSet A
  A-set = prop-set (λ x y → sym (h x) ∙ h y)

  lemma : {c c′ : A} (p : c ≡ c′) (k : (y : A) → c ≡ y) (k′ : (y : A) → c′ ≡ y)
        → (c , k) ≡ (c′ , k′)
  lemma {c} refl k k′ = ap (λ j → c , j) (fe (λ y → A-set c y (k y) (k′ y)))

equiv-is-prop : ∀ {a} → FunExt₂ a a → {A B : Set a} (f : A → B)
              → IsProp (IsEquiv f)
equiv-is-prop fe f e e′ = fe (λ y → contr-is-prop fe (e y) (e′ y))

product-is-prop :
  {@♭ ℓ : Level} → FunExt₂ ℓ ℓ → {@♭ X Y : Set ℓ}
  (@♭ sX : ShapeData X) (@♭ sY : ShapeData Y) (@♭ sXY : ShapeData (X × Y))
  → IsProp (PreservesProduct sX sY sXY)
product-is-prop fe sX sY sXY = equiv-is-prop fe (compare sX sY sXY)
