{-# OPTIONS --cohesion --without-K --flat-split #-}

-- An ordinary parameter of DISCRETE type whose level is independent of the
-- level of the shape. Claude (Fable), 13 November 2026; after fable-impl-16
-- (HANDOFF-33 item 2; NEXT-NATIVE-CLASSIFIER-GATE-01 section 2).
-- Postulate-free; no function extensionality; no reflection.
--
-- DiscreteParameters.Parameter has the index J, the shape and the targets
-- at ONE level. Here
--
--   X : Set ℓ,  s : ShapeData X          the shape, at ℓ
--   J : Set j,  J-discrete : Discrete J  the INDEX, at any level j
--   D : J → Set ℓ                        the targets, still at ℓ
--   f : (u : J) → X → D u
--
--   rec-at u       the recursor of s into D u, at a CRISP u : J
--   rec-param u    the same at an ORDINARY u, by induction on the discrete
--                  type J (GlobalPrecohesion.discrete-elim)
--   rec-param-β    at a crisp u it is rec-at u
--   rec-param-η    rec-param u (η s x) ≡ f u x  for ordinary u
--
-- The definitions are those of DiscreteParameters.Parameter with one level
-- more; rec-param-β is the computation rule used inside its rec-param-η,
-- exported. IndexedParameterSameLevel compares the two modules at j = ℓ.
--
-- WHAT THE EXTRA LEVEL IS, AND IS NOT. Only the level of J is free. At
-- every crisp u the target D u is at the level of s, so the recursor that
-- s already has is the one used; the motive of the induction on J is
--   λ u → ʃ s → D u : J → Set ℓ
-- and discrete-elim has always allowed a motive at any level. So this is
-- not a larger-target statement: no LargeOn certificate is consumed or
-- produced, and a family D at a level above ℓ is not accepted
-- (IndexedParameterLargeTarget is one such application, refused).
--
-- AN ADDITIVE MODULE. DiscreteParameters is not changed. It is accepted
-- code with its one-level contract stated in its header, and its
-- ProductStage uses Parameter at one level. The cost of not generalising
-- it in place is about a dozen repeated lines and the comparison.
module IndexedParameter where

open import Foundations
open import GlobalPrecohesion
  using (ShapeData; ʃ; η; rec; rec-η; discrete-elim; discrete-elim-β)

module Parameter
  {@♭ j ℓ : Level}
  {@♭ X : Set ℓ} (@♭ s : ShapeData X)
  {@♭ J : Set j} (@♭ J-discrete : Discrete J)
  (@♭ D : J → Set ℓ)
  (@♭ D-set : (u : J) → IsSet (D u))
  (@♭ D-discrete : (@♭ u : J) → Discrete (D u))
  (@♭ f : (u : J) → X → D u) where

  rec-at : (@♭ u : J) → ʃ s → D u
  rec-at u = rec s (D u) (D-set u) (D-discrete u) (f u)

  rec-param : (u : J) → ʃ s → D u
  rec-param = discrete-elim J-discrete (λ u → ʃ s → D u) rec-at

  rec-param-β : (@♭ u : J) → rec-param u ≡ rec-at u
  rec-param-β = discrete-elim-β J-discrete (λ u → ʃ s → D u) rec-at

  rec-param-η : (u : J) (x : X) → rec-param u (η s x) ≡ f u x
  rec-param-η = discrete-elim J-discrete
    (λ u → (x : X) → rec-param u (η s x) ≡ f u x)
    (λ u x → ap (λ h → h (η s x)) (rec-param-β u)
           ∙ rec-η s (D u) (D-set u) (D-discrete u) (f u) x)
