{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A binary sum of discrete types is discrete, and a SUPPLIED small
-- propositional truncation of a discrete type is discrete.
-- Claude (Fable), 14 November 2026; fable-impl-20 (HANDOFF-36, section 4;
-- SMALL-BASE-TRUNCATION-BRIDGE-01, section 1, whose recipe the second
-- lemma follows; BASE-CLASSIFIER-BOUNDED-MEET-02, section 4).
--
-- Nothing is postulated. No definition of this module takes or uses
-- function extensionality, propositional extensionality, a shape or a
-- choice principle. That is a statement about what is USED: the import
-- GlobalPropositions, from which the record type Truncation comes, also
-- defines the type FunExt₂ and imports GlobalPrecohesion, where the type
-- ShapeData is defined.
--
-- THE TRUNCATION IS SUPPLIED. tau : GlobalPropositions.Truncation ℓ is a
-- record with four fields: the type former at level ℓ, the unit, the proof
-- that the result is a proposition, and the recursor into propositions of
-- THE SAME level ℓ. It has no computation rule, no dependent eliminator and
-- no eliminator into a larger universe, and none is used: the section law
-- below is an identification in a proposition. No truncation is
-- constructed here, and no element is chosen from one.
--
-- _⊎_ is an ordinary inductive type. The tree had none (DecidableData.Dec
-- is the sum of a type and its negation).
module TruncationDiscrete where

open import Foundations
open import DiscretePullback using (counit-section-discrete)
open import NativeFlatIdentity using (flat-prop)
open import GlobalPropositions using (Truncation)

------------------------------------------------------------------------
-- 1. Binary sums.

infixr 1 _⊎_

data _⊎_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- A point of the sum is sent to the box of the same injection of a crisp
-- point; the stored inverse of the counit of each summand finds that point.
module SumDiscrete {@♭ a : Level} {@♭ A B : Set a}
  (@♭ dA : Discrete A) (@♭ dB : Discrete B) where

  lift : A ⊎ B → ♭ (A ⊎ B)
  lift (inl x) = flat-map inl (inverse dA x)
  lift (inr y) = flat-map inr (inverse dB y)

  lift-section : (z : A ⊎ B) → counit (lift z) ≡ z
  lift-section (inl x) =
    flat-map-counit inl (inverse dA x) ∙ ap inl (section dA x)
  lift-section (inr y) =
    flat-map-counit inr (inverse dB y) ∙ ap inr (section dB y)

  discrete : Discrete (A ⊎ B)
  discrete = counit-section-discrete lift lift-section

sum-discrete : {@♭ a : Level} {@♭ A B : Set a}
             → (@♭ dA : Discrete A) (@♭ dB : Discrete B)
             → Discrete (A ⊎ B)
sum-discrete = SumDiscrete.discrete

------------------------------------------------------------------------
-- 2. The truncation of a crisp discrete type, for a crisp truncation
--    structure. The recursor is used once, into ♭ ∥ A ∥: a type of level ℓ,
--    and a proposition because ♭ of a crisp proposition is one
--    (NativeFlatIdentity.flat-prop; the proof squash is crisp).

module TruncationIsDiscrete {@♭ ℓ : Level} (@♭ tau : Truncation ℓ)
  {@♭ A : Set ℓ} (@♭ dA : Discrete A) where

  open Truncation tau

  lift-point : A → ♭ ∥ A ∥
  lift-point x = flat-map ∣_∣ (inverse dA x)

  lift : ∥ A ∥ → ♭ ∥ A ∥
  lift = ∥-rec (flat-prop squash) lift-point

  -- No computation rule of the recursor: both sides are in a proposition.
  lift-section : (t : ∥ A ∥) → counit (lift t) ≡ t
  lift-section t = squash (counit (lift t)) t

  discrete : Discrete ∥ A ∥
  discrete = counit-section-discrete lift lift-section

truncation-discrete : {@♭ ℓ : Level} (@♭ tau : Truncation ℓ)
                    → {@♭ A : Set ℓ} (@♭ dA : Discrete A)
                    → Discrete (Truncation.∥_∥ tau A)
truncation-discrete tau dA = TruncationIsDiscrete.discrete tau dA
