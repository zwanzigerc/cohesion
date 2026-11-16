{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Assembly of a whole closed reindexing diagram: acceptance test A of
-- GENERIC-MAIN-SCHEMA-ADEQUACY-01 section 5, at the scope of
-- FABLE-REVIEW-05 section 4 (fields A1 to A8). fable-impl-08.
--
-- The diagram: B = C = Bool, the constant map collapse : Bool → Bool, the
-- closed family Family over Bool. The user writes two captures and no
-- shape data:
--   captured-B   shape of the total space  Σ Bool Family
--   captured-C   shape of the total space  Σ Bool (Family ∘ collapse)
-- Everything else is derived, under function extensionality:
--   sB, sC       terminal shape data of the two totals        (ClosedBridge)
--   relB, relC   the relative reflections over Bool, with the carriers and
--                units of sB, sC                              (TotalConverse)
--   Assembled    their canonical comparison, in total and in fibre form
--                                             (ShapeReindexing, ReindexingAssembly)
--
-- NO THEOREM OF THE PAPER IS PROVED OR PORTED HERE. The conclusion of the
-- local-connectedness theorem for this diagram is a HYPOTHESIS of the
-- module WithKernel, in the total form in which a proof about whole
-- objects delivers it: the canonical map
--     shape (Σ Bool (Family ∘ collapse)) → shape (Σ Bool Family) ×_Bool Bool
-- is an equivalence. From it the client receives
--   assembled   the fibre form for the assembled payloads, and
--   declared    the fibre form for the INDEPENDENTLY DECLARED payloads
--               `original`, `after-collapse` of ShapeReindexingExamples,
--               about their own canonical comparison (ReindexingChoice).
-- Products, the Nullstellensatz and continuity are not mentioned: they are
-- inputs of the future proof of the hypothesis, not of the assembly.
--
-- WHAT THIS FIXTURE CAN AND CANNOT SHOW (fable-impl-10; HANDOFF-18,
-- correction 2). The module WithKernel tests the WIRING: which comparison
-- a client receives, and that the conclusion is carried to independently
-- declared payloads. It does not test a diagram in which the comparison
-- could fail to be invertible. Both bases are Bool, whose equality is
-- decidable, and over such bases the hypothesis is a theorem of the weak
-- core with extensionality (DecidableReindexing). The module Derived
-- below says so in checked form: it discharges the hypothesis and
-- re-exports the conclusions without it. A client that does not rely on
-- that lemma needs bases for which no decision procedure is supplied:
-- ReindexingAcceptanceB.
--
-- Axioms declared in this file: two shapes, contextual-shape (0).
module ReindexingAcceptanceA where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion using (ShapeData; ʃ; Closed)
open import ClosedBridge using (closed-bridge)
open import ClosedSliceExamples using (Family; bool-discrete; bool-set)
open import PullbackSetFibers using (Pullback)
open import TotalConverse using (module Converse)
import ShapeReindexingExamples as Earlier
open Earlier using (collapse; original; after-collapse)
open import ReindexingAssembly using (module TotalForm)
open import ReindexingChoice using (module Independence)
open import BoolDecidable using (bool-dec)
open import DecidableReindexing using (module Stable)

-- The two captures. Both in the empty context.
captured-B : CapturedShape (Σ Bool Family)
captured-B = shape

captured-C : CapturedShape (Σ Bool (Family ∘ collapse))
captured-C = shape

KB : Closed (Σ Bool Family)
KB = C.Output.whole-context captured-B

KC : Closed (Σ Bool (Family ∘ collapse))
KC = C.Output.whole-context captured-C

-- The independently declared payloads, and their comparison.
module Declared = TotalForm Bool Bool bool-discrete bool-discrete
  Family collapse original after-collapse

module Client (@♭ fe : FunExtAt lzero) where

  sB : ShapeData (Σ Bool Family)
  sB = closed-bridge fe (Σ Bool Family) KB

  sC : ShapeData (Σ Bool (Family ∘ collapse))
  sC = closed-bridge fe (Σ Bool (Family ∘ collapse)) KC

  relB : RelativeShapeOver Bool bool-discrete Family
  relB = Converse.relative fe {dΓ = bool-discrete} bool-set sB

  relC : RelativeShapeOver Bool bool-discrete (Family ∘ collapse)
  relC = Converse.relative fe {dΓ = bool-discrete} bool-set sC

  module Assembled = TotalForm Bool Bool bool-discrete bool-discrete
    Family collapse relB relC

  -- The total comparison is a map between the carriers of the two closed
  -- shapes, over Bool.
  total-map : ʃ sC → Pullback (Output.projection relB) collapse
  total-map = Assembled.comparison-total

  module WithKernel (kernel : Assembled.TotalComparisonIsEquivalence) where

    assembled : Assembled.ComparisonIsEquivalence
    assembled = Assembled.FromTotal.fibres bool-set kernel

    private
      module I = Independence fe Bool Bool bool-discrete bool-discrete
        Family collapse relB original relC after-collapse

    declared : Declared.ComparisonIsEquivalence
    declared = I.fibre-form bool-set assembled

    -- What `declared` says, spelled out: every fibre of the comparison
    -- that ShapeReindexingExamples names is an equivalence.
    declared-at : (b : Bool) → IsEquiv (Earlier.boolean-comparison b)
    declared-at = declared

  -- For THIS diagram the hypothesis is a theorem: the bases have decidable
  -- equality. No continuity, product law or Nullstellensatz is used.
  module Derived where

    private
      module D = Stable fe Bool Bool bool-discrete bool-discrete
        bool-dec bool-dec Family collapse relB relC

    kernel : Assembled.TotalComparisonIsEquivalence
    kernel = D.total

    open WithKernel kernel public
