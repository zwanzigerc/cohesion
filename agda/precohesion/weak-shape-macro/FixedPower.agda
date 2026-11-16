{-# OPTIONS --cohesion --without-K --flat-split #-}

-- FIXED-POWER CLOSURE: a function type from a discrete type into a discrete
-- set is a discrete set, given shape data for that one function type.
-- Claude (Fable), 13 November 2026; after fable-impl-16 (HANDOFF-33 item 3;
-- NEXT-NATIVE-CLASSIFIER-GATE-01 section 3, whose plan this follows).
-- Postulate-free; no reflection; it declares nothing. A conditional theorem
-- of the library, not a schema and not a theorem of the paper.
--
-- DATA, all crisp. Levels a and c.
--   A : Set a                 A-discrete : Discrete A
--   B : Set (a ⊔ c)           B-set : IsSet B,  B-discrete : Discrete B
--   s : ShapeData (A → B)     ONE supplied terminal shape datum, at a ⊔ c
--   fe : FunExt₂ a (a ⊔ c)    extensionality for functions A → B
--
-- CONCLUSIONS (module Power).
--   fixed-power-discrete : Discrete (A → B)
--   fixed-power-set      : IsSet (A → B)
--
-- The level of B is written a ⊔ c so that A → B, s and the targets of s
-- are at one level without cumulativity and without Raise: c = lzero (or
-- c = a) is the case B : Set a, and c = lsuc a the case of a target one
-- universe above the index.
--
-- PROOF. One retract serves both conclusions.
--   1. evaluate z u : B, for z : ʃ s and an ORDINARY u : A. At a crisp u,
--      evaluation at u is a crisp map (A → B) → B into a discrete set of
--      the level of s, so the recursor of s applies; an ordinary u is
--      reached by induction on the discrete type A. This is
--      IndexedParameter.Parameter with index A : Set a and the constant
--      family B at the level a ⊔ c of s. No extensionality.
--   2. evaluate-η : evaluate (η s g) u ≡ g u, the unit law of that module.
--   3. retraction-law g : evaluate (η s g) ≡ g, from 2 by fe. This is the
--      only use of extensionality, and it turns the pointwise unit law
--      into an equality of functions A → B.
--   4. So  η s : (A → B) → ʃ s  has the crisp retraction evaluate.
--      Discreteness: RetractDiscrete.retract-discrete with ʃ-discrete s.
--      Sethood: PullbackSetFibers.retract-set, as it is, with ʃ-set s.
-- No general statement that function types preserve sets is used, and no
-- computation rule of extensionality.
--
-- WHAT IS SUPPLIED AND NOT DERIVED. s is new data for the type A → B. It is
-- not made here from shape data of A or of B, not inferred from a fibre of
-- a relative reflection, and its carrier and unit are not changed. fe is a
-- hypothesis: importing GlobalPropositions brings the TYPE FunExt₂ into
-- scope, not an inhabitant. fe has to be crisp because the retraction law
-- enters retract-discrete as a crisp term.
--
-- NOT OBTAINED: a shape of A → B; discreteness of A → B without s; anything
-- for a family of powers or for a dependent product; any product law; any
-- change of universe. A is not asked to be a set. The index A is discrete:
-- a power of a discrete set by an ARBITRARY type is not treated. That η s
-- is an equivalence is not proved and not needed; only evaluate ∘ η s ≡ id
-- is used.
module FixedPower where

open import Foundations
open import GlobalPrecohesion using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η)
open import GlobalPropositions using (FunExt₂)
open import PullbackSetFibers using (retract-set)
open import RetractDiscrete using (retract-discrete)
import IndexedParameter

------------------------------------------------------------------------
-- 1. Evaluation of a point of the shape of A → B at an ordinary argument.
--    No extensionality.

module Evaluation
  {@♭ a : Level} (@♭ c : Level)
  {@♭ A : Set a} {@♭ B : Set (a ⊔ c)}
  (@♭ A-discrete : Discrete A)
  (@♭ B-set : IsSet B) (@♭ B-discrete : Discrete B)
  (@♭ s : ShapeData (A → B)) where

  private
    module P = IndexedParameter.Parameter s A-discrete
      (λ _ → B) (λ _ → B-set) (λ _ → B-discrete) (λ u g → g u)

  evaluate : ʃ s → A → B
  evaluate z u = P.rec-param u z

  evaluate-η : (g : A → B) (u : A) → evaluate (η s g) u ≡ g u
  evaluate-η g u = P.rec-param-η u g

------------------------------------------------------------------------
-- 2. The retract, and the two conclusions from it.

module Power
  {@♭ a : Level} (@♭ c : Level)
  {@♭ A : Set a} {@♭ B : Set (a ⊔ c)}
  (@♭ A-discrete : Discrete A)
  (@♭ B-set : IsSet B) (@♭ B-discrete : Discrete B)
  (@♭ s : ShapeData (A → B))
  (@♭ fe : FunExt₂ a (a ⊔ c)) where

  open Evaluation c A-discrete B-set B-discrete s public

  -- The only use of extensionality.
  retraction-law : (g : A → B) → evaluate (η s g) ≡ g
  retraction-law g = fe (evaluate-η g)

  fixed-power-discrete : Discrete (A → B)
  fixed-power-discrete =
    retract-discrete (η s) evaluate retraction-law (ʃ-discrete s)

  fixed-power-set : IsSet (A → B)
  fixed-power-set = retract-set (η s) evaluate retraction-law (ʃ-set s)
