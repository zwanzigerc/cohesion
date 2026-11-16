{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Decidable equality for packed contexts with a DEPENDENT tail.
-- Claude (Fable), 13 November 2026; fable-impl-06. HANDOFF-06 item 6
-- ("dependent-telescope decidability"); FABLE-REVIEW-03.txt section 8.5.
-- Postulate-free.
--
-- DecidableBase.context-dec covers a packed context whose tail does not
-- depend on its head. Here: if A has decidable equality, and B x has for
-- every crisp x, then CrispΣ A B has. Together with unit-at-dec this
-- gives decidable equality for the packed context of every crisp
-- telescope whose types have decidable equality, in particular for the
-- contexts in which DecidableBase.CaptureFibre turns a fresh capture into
-- terminal shape data at the current point.
--
-- The one point that is not routine. For a dependent tail, injectivity of
-- `pair` in its second argument cannot be had by a second projection:
-- B takes its argument crisply, and the head of an ordinary element of
-- CrispΣ A B is not crisp. Instead, the tail is read AT a given crisp
-- head x by a function into B x that compares heads with the decision
-- procedure of A and returns a default when they differ. At equal heads it
-- returns the tail, whichever proof of x ≡ x the procedure produced,
-- because A is a set (Hedberg, DecidableBase.decidable-set).
--
-- --flat-split is used as in DecidableBase: to match a crisp decision
-- against `yes refl`, which identifies two crisp variables, and in
-- crisp-transport.
module DecidableTelescope where

open import Foundations
open import CaptureContext using (CrispΣ; pair; unpack)
open import DecidableBase
  using (⊥; absurd; Dec; yes; no; DecEq; decidable-set)

private
  -- Transport in a family that takes its argument crisply, along a crisp
  -- path between two crisp points. Both points are variables, so matching
  -- the path against refl identifies them.
  crisp-transport : {@♭ a : Level} {c : Level} {@♭ X : Set a}
                  → (F : (@♭ x : X) → Set c)
                  → (@♭ x x′ : X) (@♭ q : x ≡ x′) → F x → F x′
  crisp-transport F x .x refl u = u

module _ {@♭ a b : Level} {@♭ A : Set a} {@♭ B : (@♭ x : A) → Set b}
  (@♭ dA : DecEq A) (@♭ dB : (@♭ x : A) → DecEq (B x)) where

  private
    head : CrispΣ A B → A
    head = unpack (λ x _ → x)

    -- The tail of pair x′ y′ read at the head x: y′ if the heads agree, the
    -- default y₀ otherwise.
    pick : (@♭ x x′ : A) (@♭ d : Dec (x′ ≡ x)) (@♭ y₀ : B x) (@♭ y′ : B x′)
         → B x
    pick x .x (yes refl) y₀ y′ = y′
    pick x x′ (no _) y₀ y′ = y₀

    tail-at : (@♭ x : A) (@♭ y₀ : B x) → CrispΣ A B → B x
    tail-at x y₀ (pair x′ y′) = pick x x′ (dA x′ x) y₀ y′

    -- At equal heads `pick` returns the tail for EVERY decision d, not only
    -- for yes refl.
    pick-same : (@♭ x : A) (@♭ d : Dec (x ≡ x)) (@♭ y₀ y′ : B x)
              → pick x x d y₀ y′ ≡ y′
    pick-same x (yes p) y₀ y′ =
      crisp-transport (λ r → pick x x (yes r) y₀ y′ ≡ y′) refl p
        (sym (decidable-set dA x x p refl)) refl
    pick-same x (no n) y₀ y′ = absurd (n refl)

    tail-injective : (@♭ x : A) (@♭ y y′ : B x)
                   → pair {B = B} x y ≡ pair x y′ → y ≡ y′
    tail-injective x y y′ e =
      sym (pick-same x (dA x x) y y)
      ∙ ap (tail-at x y) e
      ∙ pick-same x (dA x x) y y′

    tails : (@♭ x : A) (@♭ y y′ : B x) (@♭ d : Dec (y ≡ y′))
          → Dec (pair {B = B} x y ≡ pair x y′)
    tails x y .y (yes refl) = yes refl
    tails x y y′ (no n) = no (λ e → n (tail-injective x y y′ e))

    heads : (@♭ x x′ : A) (@♭ d : Dec (x ≡ x′)) (@♭ y : B x) (@♭ y′ : B x′)
          → Dec (pair {B = B} x y ≡ pair x′ y′)
    heads x .x (yes refl) y y′ = tails x y y′ (dB x y y′)
    heads x x′ (no n) y y′ = no (λ e → n (ap head e))

  dependent-context-dec : DecEq (CrispΣ A B)
  dependent-context-dec (pair x y) (pair x′ y′) = heads x x′ (dA x x′) y y′
