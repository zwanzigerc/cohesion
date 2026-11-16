{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Target-style client A of the assembly library: CLOSED diagrams.
-- Claude (Fable), 13 November 2026; fable-impl-11.
--
-- Parts marked GENERATED are what the frontend of step S2 is to produce
-- from the user's diagram; here they are TYPED IN. There is no generator
-- in this snapshot. Parts marked USER are what a user writes.
--
-- Two diagrams.
--   1. step : Col → Row with the family Cell. Row and Col are fixed
--      abstract discrete sets for which no decision procedure is supplied,
--      and Cell has arbitrary fibres (DependentDiagramFixtures). The
--      conclusion is CONDITIONAL on Kernel, an ordinary hypothesis. From
--      these inputs the decidable-base lemma cannot be instantiated; that
--      is a statement about what is supplied, not a proof that Kernel
--      cannot be derived.
--   2. collapse : Bool → Bool with the family Colours. Both bases have
--      decidable equality, so the conclusion holds with no hypothesis
--      (the export `decidable`). A wiring test.
--
-- Declarations of this file: four shapes. Two are the generated captures
-- of the total sources of diagram 1, two those of diagram 2. Diagram 1
-- also uses two closed slice declarations, made in AssemblyClientAPayloads
-- (imported), as a second, independent choice of reflections.
module AssemblyClientA where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion using (ShapeData)
open import ClosedBridge using (closed-bridge)
open import TotalConverse using (module Converse)
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)
open import DependentDiagramFixtures
  using (Row; Col; row-discrete; row-set; col-discrete; col-set; step; Cell)
open import AssemblyFixtures using (collapse; Colours)
open import ReindexingAssembly using (module TotalForm)
open import DiagramBundle
open import AssemblyClientAPayloads using (sliceB; sliceC)

------------------------------------------------------------------------
-- GENERATED for diagram 1: two captures in the empty context, one value.

cells-B : CapturedShape (Σ Row Cell)
cells-B = shape

cells-C : CapturedShape (Σ Col (Cell ∘ step))
cells-C = shape

cells : ClosedDiagram lzero
cells = closed-diagram Row Col row-discrete row-set col-discrete col-set
  step Cell
  (C.Output.whole-context cells-B) (C.Output.whole-context cells-C)

-- GENERATED for diagram 2.

colours-B : CapturedShape (Σ Bool Colours)
colours-B = shape

colours-C : CapturedShape (Σ Bool (Colours ∘ collapse))
colours-C = shape

colours : ClosedDiagram lzero
colours = closed-diagram Bool Bool
  bool-is-discrete bool-is-set bool-is-discrete bool-is-set
  collapse Colours
  (C.Output.whole-context colours-B) (C.Output.whole-context colours-C)

-- The fields are the user's data on the nose.
same-map : ClosedField.f cells ≡ step
same-map = refl

same-family : ClosedField.A cells ≡ Cell
same-family = refl

------------------------------------------------------------------------
-- USER, diagram 1.

module Cells (@♭ fe : FunExtAt lzero) where

  module D = AssembleClosed fe cells

  -- Default outputs: the canonical comparison of the diagram, natively
  -- typed, and its unit law.
  comparison : (k : Col)
             → Output.family D.reflC k → Output.family D.reflB (step k)
  comparison = D.Diagram.comparison

  unit-law : (k : Col) (a : Cell (step k))
           → comparison k (Output.family-unit D.reflC k a)
             ≡ Output.family-unit D.reflB (step k) a
  unit-law = D.Diagram.comparison-on-unit

  -- The conclusion, from the kernel statement about the whole diagram.
  -- kernel is an ordinary argument.
  result : D.Kernel → (k : Col) → IsEquiv (comparison k)
  result = D.from-kernel

  -- The whole interface: Kernel is the total-form statement about the
  -- public module Whole, which is the comparison of the raw reflections.
  kernel-is : D.Kernel ≡ D.Whole.TotalComparisonIsEquivalence
  kernel-is = refl

  -- The same conclusion for the raw reflections, in the library's terms,
  -- and restated in the client's terms. This restatement is checked in
  -- seconds; that is an observation about this statement, not a promise
  -- for every restatement of a raw result.
  raw-result : D.Kernel → D.Whole.ComparisonIsEquivalence
  raw-result = D.raw-from-kernel

  raw-result-restated : D.Kernel → (k : Col) → IsEquiv (D.Whole.comparison k)
  raw-result-restated = D.raw-from-kernel

  -- Raw and default outputs: compared canonically, fibre by fibre, with
  -- the unit laws; equal propositionally; not equal by definition.
  to-default : (k : Col)
             → Output.family D.raw-reflC k → Output.family D.reflC k
  to-default = D.BridgeC.forward

  to-default-unit : (k : Col) (a : Cell (step k))
                  → to-default k (Output.family-unit D.raw-reflC k a)
                    ≡ Output.family-unit D.reflC k a
  to-default-unit = D.BridgeC.forward-on-unit

  default-is-raw : D.reflC ≡ D.raw-reflC
  default-is-raw = D.reflC-path

  -- The two comparisons commute with the bridges, on total spaces. The
  -- four modules named here are the ones the library instantiates once.
  commute : (z : Output.Total D.raw-reflC)
          → D.Diagram.comparison-total (D.TotalBridgeC.forward z)
            ≡ D.Sealing.pull (D.Whole.comparison-total z)
  commute = D.natural

  -- Sealing.pull is the B-side bridge applied in each fibre.
  pull-is : (k : Col) (w : Output.family D.raw-reflB (step k))
          → D.Sealing.pull (k , w) ≡ (k , D.BridgeB.forward (step k) w)
  pull-is k w = D.pull-is (k , w)

  -- A second, independent choice of reflections: two closed slice
  -- declarations. The same Kernel gives the conclusion for their
  -- comparison, and a proof of the statement for them gives Kernel.
  module Slices = D.ForPayloads sliceB sliceC

  slice-result : D.Kernel → (k : Col) → IsEquiv (Slices.Chosen.comparison k)
  slice-result = Slices.from-kernel′

  module Back = D.KernelFrom sliceB sliceC

  kernel-from-slices : Back.Supplied.TotalComparisonIsEquivalence → D.Kernel
  kernel-from-slices = Back.kernel

  ----------------------------------------------------------------------
  -- THE BOUNDARY OF THE OPAQUE PAYLOADS. The library derives its
  -- reflections from opaque copies of the supplied payloads. A client
  -- that works with the reflections derived from the ORIGINAL supplied
  -- payloads (same two steps: ClosedBridge, TotalConverse) reaches the
  -- library through KernelFrom: ORDINARY evidence about the original
  -- comparison gives the public Kernel, and from-kernel the conclusion.
  -- This is the canonical-choice route (ReindexingChoice); no transport
  -- along payloadB-path is involved.
  originalB : RelativeShapeOver Row row-discrete Cell
  originalB = Converse.relative fe {dΓ = row-discrete} row-set
    (closed-bridge fe (Σ Row Cell) (ClosedField.KB cells))

  originalC : RelativeShapeOver Col col-discrete (Cell ∘ step)
  originalC = Converse.relative fe {dΓ = col-discrete} col-set
    (closed-bridge fe (Σ Col (Cell ∘ step)) (ClosedField.KC cells))

  module Original = D.KernelFrom originalB originalC

  -- The original reflections have the total carrier of the supplied
  -- payload itself, by definition. (The library's raw ones have that of
  -- its opaque copy: equal up to payloadC-path only.)
  original-carrier : Output.Total originalC ≡ Output.Total (ClosedField.KC cells)
  original-carrier = refl

  kernel-from-original : Original.Supplied.TotalComparisonIsEquivalence
                       → D.Kernel
  kernel-from-original = Original.kernel

  result-from-original : Original.Supplied.TotalComparisonIsEquivalence
                       → (k : Col) → IsEquiv (comparison k)
  result-from-original e = D.from-kernel (Original.kernel e)

------------------------------------------------------------------------
-- USER, diagram 2.

module Colouring (@♭ fe : FunExtAt lzero) where

  module D = AssembleClosed fe colours

  comparison : (b : Bool)
             → Output.family D.reflC b → Output.family D.reflB (collapse b)
  comparison = D.Diagram.comparison

  -- No hypothesis: both bases are decidable.
  unconditional : (b : Bool) → IsEquiv (comparison b)
  unconditional = D.decidable bool-dec bool-dec

  -- Hence the total-form statement for the DEFAULT outputs. It is a
  -- statement about Diagram, not Kernel: Kernel is about the raw
  -- comparison Whole, and the two are related by Sealing, not by
  -- definition.
  total : D.Diagram.TotalComparisonIsEquivalence
  total = D.Diagram.FromFibres.total unconditional
