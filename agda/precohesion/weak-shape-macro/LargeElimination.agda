{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Large elimination for a SMALL shape choice, as a HYPOTHESIS.
-- Claude (Fable), 13 November 2026; fable-impl-02. Nothing is postulated and
-- no declaration schema is provided here. This module states the contract
-- that option B of CLASSIFIER-UNIVERSE-REVIEW-01.txt (section 8) needs, and
-- proves what follows from it; FABLE-REVIEW-02.txt, section 8, explains why
-- that option is the one recommended. Nothing in the basic theory imports
-- this module.
--
-- ShapeData X, for X : Set ℓ, has its universal property against discrete
-- sets of Set ℓ only. The two-level form of the principal-filter argument
-- sends the shape of a small type into a discrete set one universe up
-- (the map T(∀_F) : T(Ω^F) → T(Ω′)). That needs the SAME carrier and unit
-- to be initial among maps into discrete sets of a larger universe.
--
--   LargeElimination L S η   the unit η : X → S is initial among crisp maps
--                            from X into discrete sets of Set (ℓ ⊔ L)
--
-- What is proved from it:
--   own       every shape datum has it at its own level (L = ℓ);
--   Map       a map from a small type to a large one induces a map of the
--             two shapes, compatible with the units;
--   Compare   an independent shape choice for the raised type, made in the
--             larger universe, is equivalent to the raised small choice,
--             compatibly with the units.
-- Without the hypothesis there is a map from the large choice to the raised
-- small one and no map back: Raise alone does not give it.
--
-- The bound is for closed absolute sources. A capture over a larger context
-- keeps the universe of that context; this hypothesis says nothing about it.
module LargeElimination where

open import Foundations
open import CaptureContext using (Raise; raise; lower; raise-lower)
open import PullbackSetFibers using (retract-set)
open import GlobalPrecohesion
open import GlobalChoice using (set-equiv)

------------------------------------------------------------------------
-- 0. Raising a discrete set gives a discrete set.

raise-set : {@♭ a b : Level} {A : Set a} → IsSet A → IsSet (Raise b A)
raise-set A-set = retract-set lower raise raise-lower A-set

private
  -- A point of the fibre of the counit of A, raised.
  lift-fibre : {@♭ a b : Level} {@♭ A : Set a} {x : A}
             → Fiber (counit {A = A}) x
             → Fiber (counit {A = Raise b A}) (raise x)
  lift-fibre (box z , p) = box (raise z) , ap raise p

  centre : {@♭ a b : Level} {@♭ A : Set a} → Discrete A
         → (y : Raise b A) → Fiber (counit {A = Raise b A}) y
  centre dA (raise x) = lift-fibre (fst (dA x))

  at-own-point : {@♭ a b : Level} {@♭ A : Set a} (dA : Discrete A)
               → (u : ♭ (Raise b A)) → centre dA (counit u) ≡ (u , refl)
  at-own-point dA (box (raise x)) = ap lift-fibre (snd (dA x) (box x , refl))

  contract : {@♭ a b : Level} {@♭ A : Set a} (dA : Discrete A)
           → (y : Raise b A) (u : ♭ (Raise b A)) (q : counit u ≡ y)
           → centre dA y ≡ (u , q)
  contract dA .(counit u) u refl = at-own-point dA u

raise-discrete : {@♭ a b : Level} {@♭ A : Set a}
               → Discrete A → Discrete (Raise b A)
raise-discrete dA y = centre dA y , λ w → contract dA y (fst w) (snd w)

------------------------------------------------------------------------
-- 1. The statement, for a carrier and a unit.

module _ {@♭ ℓ : Level} (@♭ L : Level) {@♭ X : Set ℓ}
  (@♭ S : Set ℓ) (@♭ η₀ : X → S) where

  LargeRecursor : Set (lsuc (ℓ ⊔ L))
  LargeRecursor =
    (@♭ D : Set (ℓ ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → (@♭ f : X → D) → S → D

  LargeComputes : (@♭ r : LargeRecursor) → Set (lsuc (ℓ ⊔ L))
  LargeComputes r =
    (@♭ D : Set (ℓ ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → (@♭ f : X → D) (x : X) → r D D-set D-discrete f (η₀ x) ≡ f x

  LargeUnique : Set (lsuc (ℓ ⊔ L))
  LargeUnique =
    (@♭ D : Set (ℓ ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → (@♭ g g′ : S → D) (@♭ e : (x : X) → g (η₀ x) ≡ g′ (η₀ x))
    → (z : S) → g z ≡ g′ z

  data LargeElimination : Set (lsuc (ℓ ⊔ L)) where
    large : (@♭ r : LargeRecursor) (@♭ r-η : LargeComputes r)
          → (@♭ u : LargeUnique) → LargeElimination

  large-rec : (@♭ up : LargeElimination) → LargeRecursor
  large-rec (large r _ _) = r

  large-rec-η : (@♭ up : LargeElimination) → LargeComputes (large-rec up)
  large-rec-η (large _ r-η _) = r-η

  large-unique : (@♭ up : LargeElimination) → LargeUnique
  large-unique (large _ _ u) = u

-- For shape data.
LargeFor : {@♭ ℓ : Level} (@♭ L : Level) {@♭ X : Set ℓ}
         → (@♭ s : ShapeData X) → Set (lsuc (ℓ ⊔ L))
LargeFor L s = LargeElimination L (ʃ s) (η s)

-- At its own level this is the universal property the datum already has.
own : {@♭ ℓ : Level} {@♭ X : Set ℓ} (@♭ s : ShapeData X) → LargeFor ℓ s
own s = large (rec s) (rec-η s) (unique s)

------------------------------------------------------------------------
-- 2. Functoriality across two universes.

module Map {@♭ ℓ : Level} (@♭ L : Level)
  {@♭ X : Set ℓ} {@♭ Y : Set (ℓ ⊔ L)}
  (@♭ s : ShapeData X) (@♭ up : LargeFor L s)
  (@♭ t : ShapeData Y) (@♭ f : X → Y) where

  map↑ : ʃ s → ʃ t
  map↑ = large-rec L (ʃ s) (η s) up (ʃ t) (ʃ-set t) (ʃ-discrete t)
           (λ x → η t (f x))

  map↑-η : (x : X) → map↑ (η s x) ≡ η t (f x)
  map↑-η = large-rec-η L (ʃ s) (η s) up (ʃ t) (ʃ-set t) (ʃ-discrete t)
             (λ x → η t (f x))

------------------------------------------------------------------------
-- 3. A small choice against an independent choice for the raised type in
--    the larger universe.

-- Without any hypothesis there is a comparison in one direction.
module Raised {@♭ ℓ : Level} (@♭ L : Level) {@♭ X : Set ℓ}
  (@♭ s : ShapeData X) (@♭ t : ShapeData (Raise L X)) where

  R : Set (ℓ ⊔ L)
  R = Raise L (ʃ s)

  R-set : IsSet R
  R-set = raise-set (ʃ-set s)

  R-discrete : Discrete R
  R-discrete = raise-discrete (ʃ-discrete s)

  forward : ʃ t → Raise L (ʃ s)
  forward = rec t R R-set R-discrete (λ r → raise (η s (lower r)))

  forward-η : (r : Raise L X) → forward (η t r) ≡ raise (η s (lower r))
  forward-η = rec-η t R R-set R-discrete (λ r → raise (η s (lower r)))

-- With large elimination for the small choice it is an equivalence.
module Compare {@♭ ℓ : Level} (@♭ L : Level) {@♭ X : Set ℓ}
  (@♭ s : ShapeData X) (@♭ up : LargeFor L s)
  (@♭ t : ShapeData (Raise L X)) where

  open Raised L s t public

  private
    down : ʃ s → ʃ t
    down = large-rec L (ʃ s) (η s) up (ʃ t) (ʃ-set t) (ʃ-discrete t)
             (λ x → η t (raise x))

    down-η : (x : X) → down (η s x) ≡ η t (raise x)
    down-η = large-rec-η L (ʃ s) (η s) up (ʃ t) (ʃ-set t) (ʃ-discrete t)
               (λ x → η t (raise x))

  backward : Raise L (ʃ s) → ʃ t
  backward z = down (lower z)

  backward-η : (x : X) → backward (raise (η s x)) ≡ η t (raise x)
  backward-η = down-η

  private
    up-and-down : (z : ʃ s) → forward (down z) ≡ raise z
    up-and-down = large-unique L (ʃ s) (η s) up R R-set R-discrete
      (λ z → forward (down z)) raise
      (λ x → ap forward (down-η x) ∙ forward-η (raise x))

  forward-backward : (z : Raise L (ʃ s)) → forward (backward z) ≡ z
  forward-backward (raise z) = up-and-down z

  backward-forward : (w : ʃ t) → backward (forward w) ≡ w
  backward-forward = unique t (ʃ t) (ʃ-set t) (ʃ-discrete t)
    (λ w → backward (forward w)) (λ w → w)
    (λ r → ap backward (forward-η r)
         ∙ down-η (lower r)
         ∙ ap (η t) (raise-lower r))

  forward-is-equiv : IsEquiv forward
  forward-is-equiv = set-equiv R-set backward forward-backward backward-forward
