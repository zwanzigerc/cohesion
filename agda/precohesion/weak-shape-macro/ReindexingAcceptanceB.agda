{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A reindexing diagram in a DEPENDENT OPEN crisp context: acceptance test B
-- of GENERIC-MAIN-SCHEMA-ADEQUACY-01 section 5, with field B9 of
-- FABLE-REVIEW-05 section 4 as specified in HANDOFF-17 section 3 and
-- FABLE05-ASSEMBLY-REVIEW-01 section 3. fable-impl-10.
--
-- THE SETTING. A module with two crisp term variables
--     (@♭ b : Bool) (@♭ v : Code b)
-- (the type of the second depends on the first), and in it a diagram that
-- depends on both: local bases BaseB b v and BaseC b v, a map
-- baseMap b v : BaseC b v → BaseB b v, and a source family Fam b v over
-- BaseB b v. The local bases are discrete SETS FOR WHICH NO DECISION
-- PROCEDURE IS SUPPLIED (abstract fixtures, see DependentDiagramFixtures);
-- the fibres of Fam are arbitrary types.
--
-- WHAT THE USER WRITES. Two fresh captures in that context, of the two
-- local total sources, and no shape data:
--   captured-B   shape of  Σ (BaseB b v) (Fam b v)
--   captured-C   shape of  Σ (BaseC b v) (Fam b v ∘ baseMap b v)
--
-- WHAT IS DERIVED, under function extensionality, in this file by hand
-- (this wiring is what the automatic-assembly milestone has to generate):
--   Packed       the whole diagram over the packed context Ctx of (b , v):
--                bases Σ Ctx B̃, Σ Ctx C̃, the whole map, the whole family
--   wholeB, wholeC   terminal shape data of the two whole total sources,
--                from the payloads of the two captures (TotalBridge) and
--                the source identifications toB/fromB, toC/fromC, which
--                undo the packing and the Raise of the captured family
--   S            the whole comparison and, at the current point g₀ of the
--                context, the local comparison (ContextSpecialisation)
--   MB, MC       the local relative reflections that the two captures
--                give AT THE CURRENT POINT, with the carriers and units of
--                the captures (DecidableBase.CaptureFibre, TotalConverse)
--
-- NO THEOREM IS PROVED OR PORTED HERE. The module WithKernel takes ONE
-- labelled hypothesis, the conclusion of the local-connectedness theorem
-- for the whole packed diagram, a closed diagram between the discrete
-- sets Σ Ctx C̃ and Σ Ctx B̃:
--     kernel : the canonical map
--       shape (whole total on the C side) → shape (whole total on the B side) ×_(Σ Ctx B̃) (Σ Ctx C̃)
--     is an equivalence.
-- It returns
--   restricted   the ACTUAL canonical comparison of ShapeReindexing for the
--                local diagram at (b , v) is an equivalence in every
--                fibre, for the reflections restricted from the whole ones;
--   captured     the same for the reflections MB, MC of the two fresh
--                captures at the current point: their own canonical
--                comparison, between the carriers of the two captures,
--                with its unit law.
--
-- WHAT IS AND IS NOT ASSUMED.
--  * Decidable equality: for the packed context Ctx only
--    (DecidableTelescope). None for BaseB b v, BaseC b v or their totals;
--    the whole bases Σ Ctx B̃ and Σ Ctx C̃ are sets, by sethood of the parts.
--  * The source fibres carry no sethood hypothesis.
--  * The decidable-base lemma (DecidableReindexing) cannot be
--    INSTANTIATED from these data: it needs a decision procedure for both
--    whole bases, and none is supplied. That is a statement about the
--    inputs of this client, not a proof that `kernel` is underivable.
--    `kernel` is the statement that continuity is expected to
--    prove; continuity, products and the Nullstellensatz do not occur
--    here, they are inputs of that future proof. This file does not show
--    that continuity implies `kernel`.
--  * Taking the fibre over g₀ of a comparison that is already an
--    equivalence is native reasoning; nowhere is shape asserted to commute
--    with a pullback, and no captured fibre over a point of a local base
--    is treated as a terminal reflection.
--
-- Axioms declared in this file: two shapes, contextual-shape (2).
-- Capture happens before fe is in scope: a capture packs every crisp
-- variable in scope (OpenContextExamples).
module ReindexingAcceptanceB where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import CaptureContext
  using (CrispΣ; pair; CrispUnitAt; end-at; telescope-discrete; Raise; raise)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion using (ShapeData; ʃ; η)
open import GlobalChoice using (module Along)
open import DecidableBase
  using (DecEq; decidable-set; context-dec; unit-at-dec; module CaptureFibre)
open import DecidableTelescope using (dependent-context-dec)
open import BoolDecidable using (bool-dec)
open import DependentContextFixtures using (Code; code-dec)
open import DependentDiagramFixtures
open import TotalBridge using (module TotalData)
open import TotalConverse using (module Converse)
open import ReindexingAssembly using (module TotalForm)
open import ContextSpecialisation using (module Specialise)
open import Sealed using (sealed; sealed-path)

------------------------------------------------------------------------
-- The two fresh captures, in the context of the two term variables.

module Shapes (@♭ b : Bool) (@♭ v : Code b) where

  captured-B : CapturedShape (Σ (BaseB b v) (Fam b v))
  captured-B = shape

  captured-C : CapturedShape (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  captured-C = shape

------------------------------------------------------------------------
-- The whole diagram over the packed context. Closed data.

Ctx : Set
Ctx = CrispΣ Bool (λ b → CrispΣ (Code b) (λ _ → CrispUnitAt lzero))

ctx-dec : DecEq Ctx
ctx-dec = dependent-context-dec bool-dec
  (λ b → context-dec (code-dec b) unit-at-dec)

ctx-set : IsSet Ctx
ctx-set = decidable-set ctx-dec

B̃ : Ctx → Set
B̃ (pair b (pair v end-at)) = BaseB b v

C̃ : Ctx → Set
C̃ (pair b (pair v end-at)) = BaseC b v

f̃ : (g : Ctx) → C̃ g → B̃ g
f̃ (pair b (pair v end-at)) = baseMap b v

Ã : Σ Ctx B̃ → Set
Ã (pair b (pair v end-at) , y) = Fam b v y

dB̃ : (@♭ g : Ctx) → Discrete (B̃ g)
dB̃ (pair b (pair v end-at)) = baseB-discrete b v

B̃-set : (g : Ctx) → IsSet (B̃ g)
B̃-set (pair b (pair v end-at)) = baseB-set b v

dC̃ : (@♭ g : Ctx) → Discrete (C̃ g)
dC̃ (pair b (pair v end-at)) = baseC-discrete b v

C̃-set : (g : Ctx) → IsSet (C̃ g)
C̃-set (pair b (pair v end-at)) = baseC-set b v

------------------------------------------------------------------------

module Open (@♭ fe : FunExtAt lzero) (@♭ b : Bool) (@♭ v : Code b) where

  open Shapes b v

  -- The current point of the packed context.
  g₀ : Ctx
  g₀ = pair b (pair v end-at)

  -- The source identifications: the family that a capture stores over the
  -- packed context is the Raise of the local total source; a point of its
  -- total space is a point of the whole total source, reassociated.
  private
    toB : Σ Ctx (C.Output.family captured-B) → Σ (Σ Ctx B̃) Ã
    toB (pair b′ (pair v′ end-at) , raise x) =
      (pair b′ (pair v′ end-at) , fst x) , snd x

    fromB : Σ (Σ Ctx B̃) Ã → Σ Ctx (C.Output.family captured-B)
    fromB ((pair b′ (pair v′ end-at) , y) , a) =
      pair b′ (pair v′ end-at) , raise (y , a)

    toB-fromB : (z : Σ (Σ Ctx B̃) Ã) → toB (fromB z) ≡ z
    toB-fromB ((pair b′ (pair v′ end-at) , y) , a) = refl

    fromB-toB : (w : Σ Ctx (C.Output.family captured-B)) → fromB (toB w) ≡ w
    fromB-toB (pair b′ (pair v′ end-at) , raise x) = refl

    toC : Σ Ctx (C.Output.family captured-C)
        → Σ (Σ Ctx C̃) (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w)))
    toC (pair b′ (pair v′ end-at) , raise x) =
      (pair b′ (pair v′ end-at) , fst x) , snd x

    fromC : Σ (Σ Ctx C̃) (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w)))
          → Σ Ctx (C.Output.family captured-C)
    fromC ((pair b′ (pair v′ end-at) , k) , a) =
      pair b′ (pair v′ end-at) , raise (k , a)

    toC-fromC : (z : Σ (Σ Ctx C̃) (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w))))
              → toC (fromC z) ≡ z
    toC-fromC ((pair b′ (pair v′ end-at) , k) , a) = refl

    fromC-toC : (w : Σ Ctx (C.Output.family captured-C)) → fromC (toC w) ≡ w
    fromC-toC (pair b′ (pair v′ end-at) , raise x) = refl

  -- Terminal shape data of the two whole total sources: the total spaces
  -- of the payloads of the two captures (TotalBridge), along the source
  -- identifications. Carriers and units are those of the payloads.
  wholeB : ShapeData (Σ (Σ Ctx B̃) Ã)
  wholeB = Along.along toB fromB toB-fromB fromB-toB
    (TotalData.total-data fe {dΓ = C.Output.context-discrete captured-B}
       ctx-set (C.Output.whole-context captured-B))

  wholeC : ShapeData (Σ (Σ Ctx C̃) (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w))))
  wholeC = Along.along toC fromC toC-fromC fromC-toC
    (TotalData.total-data fe {dΓ = C.Output.context-discrete captured-C}
       ctx-set (C.Output.whole-context captured-C))

  -- The whole diagram and its restriction to the current point.
  module S = Specialise fe {G = Ctx} {dG = telescope-discrete} ctx-dec
    {B = B̃} {C = C̃} dB̃ B̃-set dC̃ C̃-set f̃ Ã wholeB wholeC

  module P = S.AtPoint g₀

  -- The local reflections that the two captures give at the current point:
  -- terminal shape data of the local total sources with the carriers and
  -- units of the captures (CaptureFibre; decidability of Ctx only), made
  -- relative over the local bases (TotalConverse; sethood only).
  dataB : ShapeData (Σ (BaseB b v) (Fam b v))
  dataB = CaptureFibre.capture-data fe captured-B ctx-dec

  dataC : ShapeData (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  dataC = CaptureFibre.capture-data fe captured-C ctx-dec

  MB : RelativeShapeOver (B̃ g₀) (dB̃ g₀) (Ã ∘ (λ y → g₀ , y))
  MB = Converse.relative fe {dΓ = dB̃ g₀} (B̃-set g₀)
    {A = Ã ∘ (λ y → g₀ , y)} dataB

  MC : RelativeShapeOver (C̃ g₀) (dC̃ g₀) (Ã ∘ (λ y → g₀ , y) ∘ f̃ g₀)
  MC = Converse.relative fe {dΓ = dC̃ g₀} (C̃-set g₀)
    {A = Ã ∘ (λ y → g₀ , y) ∘ f̃ g₀} dataC

  module Q = P.ForPayloads MB MC

  -- The local diagram is the native one, and the reflections are those of
  -- the captures: checked by refl on the small data.
  same-baseB : B̃ g₀ ≡ BaseB b v
  same-baseB = refl

  same-baseC : C̃ g₀ ≡ BaseC b v
  same-baseC = refl

  same-map : (k : BaseC b v) → f̃ g₀ k ≡ baseMap b v k
  same-map k = refl

  same-family : (y : BaseB b v) → Ã (g₀ , y) ≡ Fam b v y
  same-family y = refl

  same-carrier : Output.Total MC ≡ C.Output.carrier captured-C
  same-carrier = refl

  same-unit : (x : Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
            → Output.unit MC x ≡ C.Output.unit captured-C x
  same-unit x = refl

  -- The comparison that the client is about: the canonical comparison of
  -- ShapeReindexing for the local diagram and the reflections of the two
  -- captures, with its unit law. They are EXPORTED UNDER THESE NAMES, not
  -- defined again: a second definition would be a second spelling of a
  -- large term, and comparing two spellings is what exhausts the heap
  -- (FABLE-IMPL-10.txt, section on cost).
  --   local-comparison : (k : C̃ g₀) → family MC k → family MB (f̃ g₀ k)
  --   local-comparison-on-unit :
  --     local-comparison k (family-unit MC k a) ≡ family-unit MB (f̃ g₀ k) a
  open Q.Chosen public using ()
    renaming (comparison to local-comparison;
              comparison-on-unit to local-comparison-on-unit)

  -- Its type in the terms of the open module: a map from the fibres of the
  -- carrier of captured-C to the fibres of the carrier of captured-B.
  native-type : (k : BaseC b v)
              → Output.family MC k → Output.family MB (baseMap b v k)
  native-type = local-comparison

  -- SUPPLIED KERNEL CONCLUSION. Not proved in this tree.
  module WithKernel (kernel : S.Whole.TotalComparisonIsEquivalence) where

    restricted : P.Local.ComparisonIsEquivalence
    restricted = P.fibres kernel

    captured : Q.Chosen.ComparisonIsEquivalence
    captured = Q.fibres′ kernel


  ----------------------------------------------------------------------
  -- The same result STATED IN THE TERMS OF THE OPEN MODULE. With the
  -- derived reflections MB, MC such a restatement is a second spelling of
  -- a large term and does not finish within the heap limit. With sealed
  -- reflections (Sealed) it is checked at once.

  MB′ : RelativeShapeOver (BaseB b v) (baseB-discrete b v) (Fam b v)
  MB′ = sealed MB

  MC′ : RelativeShapeOver (BaseC b v) (baseC-discrete b v)
          (λ k → Fam b v (baseMap b v k))
  MC′ = sealed MC

  module Native = TotalForm (BaseB b v) (BaseC b v)
    (baseB-discrete b v) (baseC-discrete b v) (Fam b v) (baseMap b v)
    MB′ MC′

  private
    module Q′ = P.ForPayloads MB′ MC′

  module WithKernelNative (kernel : S.Whole.TotalComparisonIsEquivalence) where

    native : (k : BaseC b v) → IsEquiv (Native.comparison k)
    native = Q′.fibres′ kernel

    native-unit : (k : BaseC b v) (a : Fam b v (baseMap b v k))
                → Native.comparison k (Output.family-unit MC′ k a)
                  ≡ Output.family-unit MB′ (baseMap b v k) a
    native-unit = Native.comparison-on-unit
