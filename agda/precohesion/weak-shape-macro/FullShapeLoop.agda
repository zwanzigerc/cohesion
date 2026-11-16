{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A test that only the FULL interface admits: a loop of the base is seen
-- in the triangle of a factorisation.
-- Claude (Fable), 14 November 2026; fable-impl-23 (HANDOFF-38).
--
-- Fix a crisp discrete type B, a crisp point b and a crisp loop
-- ρ : b ≡ b. Take the family A b′ = (b ≡ b′) and the test map
-- t : B → B constant at b. Over B there are two whole maps from the
-- source total to t with the SAME underlying function, constant at b:
--     plain    with triangle  (b′ , h) ↦ h
--     twisted  with triangle  (b′ , h) ↦ ρ ∙ h.
-- For any full shape K of this family, if the two factorisations through
-- K are equal then ρ ≡ refl. So for a loop that is not refl they are two
-- different maps over B out of the carrier: the universal property keeps
-- the information that the triangle carries.
--
-- The fibre of t over b has B as a retract (fibre-retract). So when B is
-- not a set, t does not have set fibres and is not an admissible test of
-- the Shape₀ interface; the full interface has no such condition.
--
-- The loop and the full shape are parameters. No model is claimed for a
-- crisp discrete type with a loop that is not refl, and none is needed
-- for the statement: `separates` holds for every loop.
module FullShapeLoop where

open import Foundations
open import RelativeSliceShape using (MapOver; over-map; function; triangle)
open import FlatContext using (right-unit)
open import DecidableData using (⊥)
open import FullRelativeShape

module Loop {@♭ ℓ : Level} (@♭ B : Set ℓ) (@♭ dB : Discrete B)
  (@♭ b : B) (@♭ ρ : b ≡ b) where

  A : B → Set ℓ
  A b′ = b ≡ b′

  -- The test: the constant map at b, from the discrete type B itself.
  t : B → B
  t _ = b

  plain : MapOver (fst {B = A}) t
  plain = over-map (λ _ → b) (λ a → snd a)

  twisted : MapOver (fst {B = A}) t
  twisted = over-map (λ _ → b) (λ a → ρ ∙ snd a)

  same-function : function plain ≡ function twisted
  same-function = refl

  -- Equal as whole maps only if the loop is refl.
  whole-maps-differ : plain ≡ twisted → ρ ≡ refl
  whole-maps-differ e =
    sym (right-unit ρ) ∙ sym (ap (λ f → triangle f (b , refl)) e)

  -- B is a retract of the fibre of the test over b.
  into-fibre : B → Fiber t b
  into-fibre x = x , refl

  fibre-retract : (x : B) → fst (into-fibre x) ≡ x
  fibre-retract x = refl

  module Test (@♭ K : FullShapeOver B dB A) where

    factor-plain : MapOver (FullOutput.projection K) t
    factor-plain = FullOutput.factor K B dB t plain

    factor-twisted : MapOver (FullOutput.projection K) t
    factor-twisted = FullOutput.factor K B dB t twisted

    -- The statement, for every loop.
    separates : factor-plain ≡ factor-twisted → ρ ≡ refl
    separates e = whole-maps-differ
      ( sym (FullOutput.factor-β K B dB t plain)
      ∙ ap (FullOutput.pre K B t) e
      ∙ FullOutput.factor-β K B dB t twisted )

    -- For a loop that is not refl the two factorisations are different.
    distinct : (ρ ≡ refl → ⊥) → factor-plain ≡ factor-twisted → ⊥
    distinct ρ-not-refl e = ρ-not-refl (separates e)
