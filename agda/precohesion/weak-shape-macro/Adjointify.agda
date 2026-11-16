{-# OPTIONS --safe --without-K --cohesion #-}

-- A map with a two-sided inverse up to pointwise paths is an equivalence.
-- Claude (Fable), 13 November 2026; fable-impl-03. Literally --safe.
--
-- IsEquiv is "contractible fibres". GlobalChoice.set-equiv proves it from a
-- pointwise inverse when the codomain is a set. The equivalences needed for
-- large targets are between types of crisp maps, ♭ (S → D), which are not
-- known to be sets without function extensionality. So the general
-- statement is proved here, by the usual correction of one of the two
-- homotopies (HoTT book, Theorem 4.2.3). No extensionality, no sethood.
module Adjointify where

open import Foundations

private
  right-unit : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  right-unit refl = refl

  cancel-inverse : ∀ {a} {A : Set a} {x y z : A} (p : x ≡ y) (q : y ≡ z)
                 → sym p ∙ (p ∙ q) ≡ q
  cancel-inverse refl q = refl

  cancel-right : ∀ {a} {A : Set a} {x y z : A} {p q : x ≡ y} (r : y ≡ z)
               → p ∙ r ≡ q ∙ r → p ≡ q
  cancel-right {p = p} {q = q} refl h = sym (right-unit p) ∙ h ∙ right-unit q

  ap-compose : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
             → (k : B → C) (h : A → B) {x y : A} (p : x ≡ y)
             → ap k (ap h p) ≡ ap (λ z → k (h z)) p
  ap-compose k h refl = refl

  -- A homotopy from h to the identity is natural.
  natural : ∀ {a} {A : Set a} (h : A → A) (H : (x : A) → h x ≡ x)
          → {x y : A} (p : x ≡ y) → ap h p ∙ H y ≡ H x ∙ p
  natural h H {x = x} refl = sym (right-unit (H x))

  -- Hence it agrees with its own image under h.
  at-image : ∀ {a} {A : Set a} (h : A → A) (H : (x : A) → h x ≡ x)
           → (x : A) → H (h x) ≡ ap h (H x)
  at-image h H x = cancel-right (H x) (sym (natural h H (H x)))

  fibre-path : ∀ {a b} {A : Set a} {B : Set b} {f : A → B}
             → {y : B} {x x′ : A} {p : f x ≡ y} {p′ : f x′ ≡ y}
             → (q : x ≡ x′) → ap f q ∙ p′ ≡ p → (x , p) ≡ (x′ , p′)
  fibre-path {x = x} refl h = ap (λ p → x , p) (sym h)

module _ {a b} {A : Set a} {B : Set b} {f : A → B}
  (g : B → A)
  (sec : (y : B) → f (g y) ≡ y)
  (ret : (x : A) → g (f x) ≡ x) where

  private
    -- The corrected section.
    sec′ : (y : B) → f (g y) ≡ y
    sec′ y = sym (sec (f (g y))) ∙ (ap f (ret (g y)) ∙ sec y)

    step₁ : (x : A) → ap f (ret (g (f x))) ≡ ap (λ z → f (g z)) (ap f (ret x))
    step₁ x = ap (ap f) (at-image (λ z → g (f z)) ret x)
            ∙ ap-compose f (λ z → g (f z)) (ret x)
            ∙ sym (ap-compose (λ z → f (g z)) f (ret x))

    step₂ : (x : A)
          → ap f (ret (g (f x))) ∙ sec (f x) ≡ sec (f (g (f x))) ∙ ap f (ret x)
    step₂ x = ap (λ r → r ∙ sec (f x)) (step₁ x)
            ∙ natural (λ y → f (g y)) sec (ap f (ret x))

    triangle : (x : A) → ap f (ret x) ≡ sec′ (f x)
    triangle x = sym (cancel-inverse (sec (f (g (f x)))) (ap f (ret x)))
               ∙ ap (λ r → sym (sec (f (g (f x)))) ∙ r) (sym (step₂ x))

    contraction : (x : A) (y : B) (p : f x ≡ y) → (g y , sec′ y) ≡ (x , p)
    contraction x .(f x) refl =
      fibre-path (ret x) (right-unit (ap f (ret x)) ∙ triangle x)

  quasi-inverse : IsEquiv f
  quasi-inverse y = (g y , sec′ y) , λ w → contraction (fst w) y (snd w)
