{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The large-target certificate in use. fable-impl-03; HANDOFF-06 item 5 and
-- the acceptance probes of CLASSIFIER-LARGE-UP-SCHEMA-01.txt section 8
-- (1-5, 8, 9; the classifier probe 6 is LargeTargetClassifierExample).
--
-- Axioms declared in this file: ONE certificate, up₂, for the closed payload
-- K₁ of GlobalDeclareExamples at ceiling 2, and one further closed shape
-- (`again`) used as an independent choice for the transfer test.
module LargeTargetExamples where

open import Foundations
open import CaptureContext using (Raise; raise; lower)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalPropositions using (FunExt₂)
open import GlobalChoice using (module Choice)
open import ClosedBridge using (module Existence; module Bridge)
import RelativeSliceShape as R
open import LargeElimination using (LargeFor; module Compare)
open import LargeTarget
open import LargeTargetDeclare
open import GlobalDeclareExamples using (Space₁; K₁)
open import LargeEliminationExamples using (K↑)

private
  ℓ₁ ℓ₂ : Level
  ℓ₁ = lsuc lzero
  ℓ₂ = lsuc ℓ₁

  module E₁ = Existence Space₁ K₁
  module E↑ = Existence (Raise ℓ₁ Space₁) K↑

------------------------------------------------------------------------
-- 1. The declaration: at top level, no extensionality in scope. The
--    payload K₁ was declared by fable-impl-02's example and is not changed.

unquoteDecl up₂ = declareLargeUP up₂ ℓ₂ Space₁ K₁

its-type : ClosedLargeUP ℓ₂ Space₁ K₁
its-type = up₂

------------------------------------------------------------------------
-- 2. Before any extensionality.

-- Smaller ceilings, by proof. Carrier E₁.T and unit E₁.η₀ are in the types.
up₁ : ClosedLargeUP ℓ₁ Space₁ K₁
up₁ = Restrict.restrict ℓ₁ ℓ₂ up₂

up₀ : ClosedLargeUP lzero Space₁ K₁
up₀ = Restrict.restrict lzero ℓ₁ up₁

up₀-direct : ClosedLargeUP lzero Space₁ K₁
up₀-direct = Restrict.restrict lzero ℓ₂ up₂

-- A map out of the SMALL carrier into a discrete set of Set₁ which is not
-- a raised small set: the carrier of an independent closed shape in Set₁.
into-large : E₁.T → E↑.T
into-large = MapShape.mapShape ℓ₁ up₁
  E↑.T E↑.T-set (R.Output.total-discrete K↑) E↑.η₀ raise

into-large-on-units : (x : Space₁) → into-large (E₁.η₀ x) ≡ E↑.η₀ (raise x)
into-large-on-units = MapShape.mapShape-η ℓ₁ up₁
  E↑.T E↑.T-set (R.Output.total-discrete K↑) E↑.η₀ raise

------------------------------------------------------------------------
-- 3. Two independent extensionality inputs, one carrier, one unit, one
--    certificate.

module TwoInputs (@♭ fe fe′ : FunExtAt lzero) where

  d d′ : ShapeData Space₁
  d = Bridge.data-of fe Space₁ K₁
  d′ = Bridge.data-of fe′ Space₁ K₁

  one : LargeOn ℓ₂ d
  one = attach ℓ₂ Space₁ K₁ up₂ fe

  other : LargeOn ℓ₂ d′
  other = attach ℓ₂ Space₁ K₁ up₂ fe′

  same-carrier : ʃ d ≡ ʃ d′
  same-carrier = refl

  same-unit : η d ≡ η d′
  same-unit = refl

  same-certificate : one ≡ other
  same-certificate = refl

  -- The certificate at the level of the source gives a recursor on the same
  -- carrier; it agrees with the recursor d already has. No further
  -- extensionality.
  old-recursor : (@♭ D : Set) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
               → (@♭ f : Space₁ → D) (z : ʃ d)
               → At.recLarge lzero (Old.same-level ℓ₂ d one) D D-set D-discrete f z
                 ≡ rec d D D-set D-discrete f z
  old-recursor = Old.rec-agrees ℓ₂ d one

------------------------------------------------------------------------
-- 4. With the mixed extensionality: functions from Set into Set₁.

again : CapturedShape Space₁
again = shape

K₁′ : Closed Space₁
K₁′ = C.Output.whole-context again

module WithMixed
  (@♭ fe₀ : FunExtAt lzero) (@♭ fe₁ : FunExtAt ℓ₁)
  (@♭ fe₀₁ : FunExt₂ lzero ℓ₁) where

  small : ShapeData Space₁
  small = Bridge.data-of fe₀ Space₁ K₁

  c₁ : LargeOn ℓ₁ small
  c₁ = attach ℓ₁ Space₁ K₁ up₁ fe₀

  -- The pointwise form of fable-impl-02, now derived from the declared
  -- certificate instead of assumed.
  pointwise : LargeFor ℓ₁ small
  pointwise = to-pointwise ℓ₁ fe₀₁ c₁

  big : ShapeData (Raise ℓ₁ Space₁)
  big = Bridge.data-of fe₁ (Raise ℓ₁ Space₁) K↑

  small-is-big : IsEquiv (Compare.forward ℓ₁ small pointwise big)
  small-is-big = Compare.forward-is-equiv ℓ₁ small pointwise big

  -- The raised source: shape data in Set₁ whose carrier is the raised
  -- small carrier, compared with the independent choice by GlobalChoice.
  lifted : ShapeData (Raise ℓ₁ Space₁)
  lifted = RaisedData.raised-data ℓ₁ (ʃ-set small) (ʃ-discrete small) fe₀₁ c₁

  lifted-carrier : ʃ lifted ≡ Raise ℓ₁ (ʃ small)
  lifted-carrier = refl

  lifted-is-big : IsEquiv (Choice.forward lifted big)
  lifted-is-big = Choice.forward-is-equiv lifted big

  -- The two routes of restriction to the level of the source are different
  -- proofs for the same carrier and unit; their recursors agree.
  routes-agree : (@♭ D : Set) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
               → (@♭ f : Space₁ → D) (z : E₁.T)
               → At.recLarge lzero up₀ D D-set D-discrete f z
                 ≡ At.recLarge lzero up₀-direct D D-set D-discrete f z
  routes-agree D D-set D-discrete f =
    At.recLarge-unique lzero up₀-direct D D-set D-discrete fe₀
      (At.recLarge lzero up₀ D D-set D-discrete f)
      (At.recLarge lzero up₀-direct D D-set D-discrete f)
      (λ x → At.recLarge-η lzero up₀ D D-set D-discrete f x
           ∙ sym (At.recLarge-η lzero up₀-direct D D-set D-discrete f x))

  -- Transfer to an independent choice of the same closed type, along the
  -- canonical unit-preserving equivalence of the two choices.
  small′ : ShapeData Space₁
  small′ = Bridge.data-of fe₀ Space₁ K₁′

  private
    module Ch = Choice small small′

  c₁′ : LargeOn ℓ₁ small′
  c₁′ = Transfer.transfer ℓ₁ fe₀₁ Ch.forward Ch.forward-is-equiv Ch.forward-η c₁
