{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The relative larger-target certificate in use. Claude (Fable),
-- 13 November 2026; after fable-impl-15 (HANDOFF-32, the bounded
-- acceptance; RELATIVE-LARGE-UP-IMPLEMENTATION-REVIEW-01 section 4).
--
-- The base is Bool. The source family is constant with fibre Space₁, a
-- postulated closed type of unspecified cohesion: the fibres are
-- arbitrary. The target is a discrete set of Set₁ over Bool that is not
-- GIVEN as a raised small set: one factor is the carrier of an
-- independent closed shape of a type of Set₁. (Whether that carrier is
-- equivalent to a raised small set is not used here; that the target is
-- of Set₁ is a fact about its type, not a theorem that it cannot be made
-- small: fable-impl-17.) The carrier, the unit and the projection of the
-- reflection stay in Set.
--
-- SUPPLIED DATA. Declared in this file:
--   total     one closed shape, of the total space Σ Bool (λ _ → Space₁)
--   up-total  ONE large-target certificate for that payload at ceiling 1,
--             by LargeTargetDeclare.declareLargeUP: new trusted data of
--             the large-target extension, declared in the empty context
--   Captured.whole   one shape request in a context, for section 5
-- Imported with their own declarations:
--   GlobalDeclareExamples     two postulated closed types, three closed
--                             shapes, one product statement; used here:
--                             Space₁
--   LargeEliminationExamples  one closed shape of Raise 1 Space₁; used
--                             here: its payload K↑, as a large target
-- Hypotheses: function extensionality at level ZERO, crisp, a module
-- parameter. No HYPOTHESIS of extensionality for functions into Set₁ is
-- taken anywhere in this file. (GlobalPropositions, where the type FunExt₂
-- is defined, is not imported DIRECTLY; it is in the import closure
-- through LargeTarget. fable-impl-17, after M16-SOURCE-REVIEW-01: this
-- replaces "GlobalPropositions is not imported".) In section 5 a terminal
-- certificate for an existing relative reflection is a module parameter.
-- Nothing of the Nullstellensatz extension is in the import closure.
module RelativeLargeTargetExamples where

open import Foundations
open import Agda.Builtin.Bool
open import CaptureContext using (Raise; raise; lower)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalPrecohesion
open import ClosedBridge using (module Existence; module Bridge)
import RelativeSliceShape as R
open R using (RelativeShapeOver; SliceUniversal)
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)
open import DecidableBase using (decidable-set; context-dec; unit-at-dec)
open import TotalBridge using (Σ-set; module TotalData)
open import TotalConverse using (module Converse)
open import LargeElimination using (raise-set; raise-discrete)
open import LargeTarget using (LargeOn; LargeTerminalUP)
open import LargeTargetDeclare using (ClosedLargeUP; declareLargeUP; attach)
open import MixedMapOver
open import RelativeLargeTarget
open import GlobalDeclareExamples using (Space₁)
open import LargeEliminationExamples using (K↑)

private
  ℓ₁ : Level
  ℓ₁ = lsuc lzero

  module E↑ = Existence (Raise ℓ₁ Space₁) K↑

------------------------------------------------------------------------
-- 1. The supplied terminal data, in the empty context.

Fibre : Bool → Set
Fibre _ = Space₁

X : Set
X = Σ Bool Fibre

total : CapturedShape (Σ Bool (λ _ → Space₁))
total = shape

KT : Closed X
KT = C.Output.whole-context total

unquoteDecl up-total = declareLargeUP up-total ℓ₁ X KT

its-type : ClosedLargeUP ℓ₁ X KT
its-type = up-total

------------------------------------------------------------------------
-- 2. A target of Set₁ over Bool: pairs of a raised Boolean and a point of
--    the carrier of the independent closed shape of Raise 1 Space₁.

D : Set₁
D = Σ (Raise ℓ₁ Bool) (λ _ → E↑.T)

q : D → Bool
q d = lower (fst d)

D-discrete : Discrete D
D-discrete = SigmaDiscrete.discrete (raise-discrete bool-is-discrete)
  (λ _ → R.Output.total-discrete K↑)

D-set : IsSet D
D-set = Σ-set (raise-set bool-is-set) (λ _ → E↑.T-set)

q-set-fibers : SetFibersM q
q-set-fibers = set-fibers-between-sets bool-is-set D-set q

------------------------------------------------------------------------
-- 3. The certificate. The only extensionality is at level zero.

module WithFE (@♭ fe : FunExtAt lzero) where

  s : ShapeData X
  s = Bridge.data-of fe X KT

  c : LargeOn ℓ₁ s
  c = attach ℓ₁ X KT up-total fe

  -- The relative reflection of Fibre over Bool that s gives.
  K : RelativeShapeOver Bool bool-is-discrete Fibre
  K = Converse.relative fe {dΓ = bool-is-discrete} bool-is-set s

  certificate : RelativeLargeOn ℓ₁ K
  certificate = Canonical.relative-large ℓ₁ fe bool-is-set s c

  -- The SAME carrier, unit and projection, all small.
  small-carrier : Set
  small-carrier = R.Output.Total K

  same-carrier : R.Output.Total K ≡ ʃ s
  same-carrier = refl

  payload-carrier : R.Output.Total K ≡ Existence.T X KT
  payload-carrier = refl

  same-unit : (a : X) → R.Output.unit K a ≡ η s a
  same-unit a = refl

  same-projection : (z : ʃ s)
    → R.Output.projection K z ≡ rec s Bool bool-is-set bool-is-discrete fst z
  same-projection z = refl

  -- THE CONCLUSION at the target of Set₁: precomposition with the unit of
  -- K, on boxed maps over Bool, is an equivalence.
  the-map : ♭ (MapOverM (R.Output.projection K) q)
          → ♭ (MapOverM (fst {B = Fibre}) q)
  the-map = flat-map
    (precomposeOverM ℓ₁ Bool Fibre (R.Output.Total K) (R.Output.projection K)
      (R.Output.unit K) (R.Output.unit-over K) D q)

  conclusion : IsEquiv the-map
  conclusion = certificate D D-discrete q q-set-fibers

  -- In use: a crisp map over Bool from the total source into D extends
  -- along the unit, and the extension computes on units.
  f : MapOverM (fst {B = Fibre}) q
  f = over-mapM (λ a → raise (fst a) , E↑.η₀ (raise (snd a))) (λ a → refl)

  module Into = FactorOn ℓ₁ K certificate D D-discrete q q-set-fibers

  g : MapOverM (R.Output.projection K) q
  g = Into.factor f

  -- It is the inverse of the equivalence above, at f.
  g-is : g ≡ counit (inverse conclusion (box f))
  g-is = refl

  g-over : (z : R.Output.Total K)
         → q (functionM g z) ≡ R.Output.projection K z
  g-over = triangleM g

  g-on-units : (a : X) → functionM g (R.Output.unit K a) ≡ functionM f a
  g-on-units = Into.factor-on-unit f

  ----------------------------------------------------------------------
  -- 4. Other ceilings, and the existing-reflection adapter.

  -- The ceiling of the source, by restricting the SUPPLIED terminal
  -- certificate; same carrier, unit and projection.
  at-own-level : RelativeLargeOn lzero K
  at-own-level = AtSmaller.certificate lzero ℓ₁ fe bool-is-discrete bool-is-set s
    (R.Output.projection K) (R.Output.unit-over K) c

  -- At that ceiling the mixed statement is the old one, for the old
  -- record, and K's own universal property is a certificate.
  old-form : SliceUniversal Bool Fibre (R.Output.Total K)
               (R.Output.projection K) (R.Output.unit K) (R.Output.unit-over K)
  old-form = SameLevel.to-universal Bool Fibre (R.Output.Total K)
    (R.Output.projection K) (R.Output.unit K) (R.Output.unit-over K) at-own-level

  from-own : RelativeLargeOn lzero K
  from-own = relative-own-level K

  -- The adapter for a reflection that already exists, at this K: the
  -- shape data that TotalBridge makes from K have the carrier and unit of
  -- s, so the SAME supplied certificate is accepted, unchanged.
  direct : RelativeLargeOn ℓ₁ K
  direct = Direct.relative-large ℓ₁ fe bool-is-set K c

  -- What that adapter consumes is, by computation, the terminal statement
  -- for K's OWN total space and unit; extensionality is not in it.
  consumed : LargeOn ℓ₁ (TotalData.total-data fe bool-is-set K)
           ≡ LargeTerminalUP ℓ₁ X (R.Output.Total K) (R.Output.unit K)
  consumed = refl

------------------------------------------------------------------------
-- 5. An existing relative reflection: the whole payload of a capture in a
--    context. Its base is the packed context, a set because Bool has a
--    decision procedure; its fibres are arbitrary. The terminal
--    certificate for its total data is a HYPOTHESIS here: no declaration
--    schema supplies one for an open payload, and none is added.

module Captured (@♭ b : Bool) where

  whole : CapturedShape Space₁
  whole = shape

module Existing (@♭ b : Bool) (@♭ fe : FunExtAt lzero) where

  private
    K₀ = C.Output.whole-context (Captured.whole b)

    G-set : IsSet (C.Output.context (Captured.whole b))
    G-set = decidable-set (context-dec bool-dec unit-at-dec)

  module _ (@♭ c : LargeOn ℓ₁ (TotalData.total-data fe G-set K₀)) where

    -- About the capture's own payload: nothing is replaced.
    existing : RelativeLargeOn ℓ₁ K₀
    existing = Direct.relative-large ℓ₁ fe G-set K₀ c
