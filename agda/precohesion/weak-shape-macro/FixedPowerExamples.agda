{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The fixed-power closure in use. Claude (Fable), 13 November 2026; after
-- fable-impl-16 (HANDOFF-33, the bounded client).
--
-- The index is Bool : Set. The target is a discrete set of Set₁ that is not
-- GIVEN as a raised small set: the carrier of an independent closed shape
-- of a type of Set₁. (Whether that carrier is equivalent to a raised small
-- set is not used here, and its being of Set₁ is a fact about its type,
-- not a theorem that it cannot be made small.) So a = 0, c = 1, and the
-- function type, its shape data and the extensionality are at level 1.
--
-- SUPPLIED DATA. Declared in this file:
--   power     ONE closed shape, of the function type Bool → B itself, at
--             level 1 (section 4 only)
-- Imported with their own declarations:
--   GlobalDeclareExamples     two postulated closed types, three closed
--                             shapes, one product statement; used here:
--                             Space₁
--   LargeEliminationExamples  one closed shape of Raise 1 Space₁; used
--                             here: its payload K↑, whose carrier is B
-- Hypotheses, all crisp module parameters:
--   section 3   s : ShapeData (Bool → B)  and  fe : FunExt₂ 0 1
--   section 4   fe as before, and extensionality at level 1 for the bridge
--               from the closed payload to shape data (ClosedBridge)
--   section 5   shape data of a small type
--   section 6   everything
-- No product law and no large-target certificate is used. LargeTarget and
-- the Nullstellensatz extension are not in the import closure;
-- LargeElimination is imported for raise-discrete alone.
module FixedPowerExamples where

open import Foundations
open import Agda.Builtin.Bool
open import CaptureContext using (Raise; raise; lower; raise-lower; lower-raise)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalPropositions using (FunExt₂)
open import ClosedBridge using (module Existence; module Bridge)
import RelativeSliceShape as R
open import BoolDecidable using (bool-is-discrete)
open import LargeElimination using (raise-discrete)
open import RetractDiscrete using (retract-discrete)
import IndexedParameter
import FixedPower
open import GlobalDeclareExamples using (Space₁)
open import LargeEliminationExamples using (K↑)

private
  ℓ₁ : Level
  ℓ₁ = lsuc lzero

  module E↑ = Existence (Raise ℓ₁ Space₁) K↑

------------------------------------------------------------------------
-- 1. The retract lemma at unequal levels, in both directions. No shape,
--    no extensionality.

-- A at level 1, S at level 0.
raised-bool-discrete : Discrete (Raise ℓ₁ Bool)
raised-bool-discrete =
  retract-discrete lower raise raise-lower bool-is-discrete

-- A at level 0, S at level 1: discreteness comes DOWN from the raised type.
private
  bool↑-discrete : Discrete (Raise ℓ₁ Bool)
  bool↑-discrete = raise-discrete bool-is-discrete

bool-discrete-again : Discrete Bool
bool-discrete-again =
  retract-discrete raise lower (lower-raise {b = ℓ₁}) bool↑-discrete

------------------------------------------------------------------------
-- 2. An index of Set and a target of Set₁.

B : Set₁
B = E↑.T

B-set : IsSet B
B-set = E↑.T-set

B-discrete : Discrete B
B-discrete = R.Output.total-discrete K↑

Functions : Set₁
Functions = Bool → B

------------------------------------------------------------------------
-- 3. The theorem, its data supplied as hypotheses.

module Supplied
  (@♭ s : ShapeData Functions) (@♭ fe : FunExt₂ lzero ℓ₁) where

  module P = FixedPower.Power ℓ₁ bool-is-discrete B-set B-discrete s fe

  -- THE CONCLUSIONS.
  discrete : Discrete (Bool → E↑.T)
  discrete = P.fixed-power-discrete

  is-set : IsSet (Bool → E↑.T)
  is-set = P.fixed-power-set

  -- The retract they both come from: the unit of s, and evaluation.
  evaluate : ʃ s → Bool → E↑.T
  evaluate = P.evaluate

  evaluate-on-units : (g : Bool → E↑.T) (u : Bool)
                    → evaluate (η s g) u ≡ g u
  evaluate-on-units = P.evaluate-η

  retraction-law : (g : Bool → E↑.T) → evaluate (η s g) ≡ g
  retraction-law = P.retraction-law

  -- Discreteness in use: every function is the counit of a boxed one.
  boxed : (g : Bool → E↑.T) → ♭ (Bool → E↑.T)
  boxed g = inverse discrete g

  boxed-counit : (g : Bool → E↑.T) → counit (boxed g) ≡ g
  boxed-counit g = section discrete g

------------------------------------------------------------------------
-- 4. The same with s from a closed declaration: one closed shape of the
--    function type. The bridge from a closed payload to shape data needs
--    extensionality at the level of that type; this is a hypothesis of
--    the bridge, not of the fixed-power theorem.

power : CapturedShape (Bool → E↑.T)
power = shape

KP : Closed Functions
KP = C.Output.whole-context power

module Closed
  (@♭ fe₁ : FunExtAt ℓ₁) (@♭ fe : FunExt₂ lzero ℓ₁) where

  s : ShapeData Functions
  s = Bridge.data-of fe₁ Functions KP

  module S = Supplied s fe

  discrete : Discrete (Bool → E↑.T)
  discrete = S.discrete

  is-set : IsSet (Bool → E↑.T)
  is-set = S.is-set

  -- The supplied shape is used as it is: its carrier is the carrier of
  -- the closed payload.
  same-carrier : ʃ s ≡ Existence.T Functions KP
  same-carrier = refl

------------------------------------------------------------------------
-- 5. IndexedParameter with the index ABOVE the level of the shape: a
--    shape at level 0, an index of Set₁, targets at level 0.

module LargeIndex (@♭ t : ShapeData Space₁) where

  module Q = IndexedParameter.Parameter t bool↑-discrete
    (λ _ → ʃ t) (λ _ → ʃ-set t) (λ _ → ʃ-discrete t) (λ _ x → η t x)

  at : Raise ℓ₁ Bool → ʃ t → ʃ t
  at = Q.rec-param

  at-on-units : (u : Raise ℓ₁ Bool) (x : Space₁) → at u (η t x) ≡ η t x
  at-on-units = Q.rec-param-η

------------------------------------------------------------------------
-- 6. The levels of the two uses that NEXT-NATIVE-CLASSIFIER-GATE-01
--    section 3 names, for an arbitrary crisp level i, everything a
--    hypothesis: a power at one level (c = lzero) and a power whose target
--    is one universe above its index.

module TwoUses
  {@♭ i : Level}
  {@♭ F O P : Set (lsuc i)} {@♭ O′ : Set (lsuc (lsuc i))}
  (@♭ F-discrete : Discrete F)
  (@♭ O-set : IsSet O) (@♭ O-discrete : Discrete O)
  (@♭ sQ : ShapeData (F → O))
  (@♭ feQ : FunExt₂ (lsuc i) (lsuc i))
  (@♭ P-discrete : Discrete P)
  (@♭ O′-set : IsSet O′) (@♭ O′-discrete : Discrete O′)
  (@♭ sR : ShapeData (P → O′))
  (@♭ feR : FunExt₂ (lsuc i) (lsuc (lsuc i))) where

  module Q = FixedPower.Power lzero F-discrete O-set O-discrete sQ feQ
  module R′ = FixedPower.Power (lsuc (lsuc i)) P-discrete O′-set O′-discrete sR feR

  Q-discrete : Discrete (F → O)
  Q-discrete = Q.fixed-power-discrete

  Q-set : IsSet (F → O)
  Q-set = Q.fixed-power-set

  R-discrete : Discrete (P → O′)
  R-discrete = R′.fixed-power-discrete

  R-set : IsSet (P → O′)
  R-set = R′.fixed-power-set
