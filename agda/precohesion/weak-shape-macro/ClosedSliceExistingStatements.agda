{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The nine constants that the tree declares through the reflected-term
-- entry point DeclareClosedShape.declareClosedShape, each checked at its
-- statement AS IT IS WRITTEN in the declaring file.
-- Claude (Fable), 14 November 2026; fable-impl-21
-- (FABLE-C12-RECONCILIATION-REQUEST: "preserve legitimate old examples").
--
-- Nothing is declared here: nine typed aliases, ordinary Agda. For each
-- of them the right-hand side is the constant of an existing example and
-- the type signature is the statement copied from the quoteTerm of its
-- declaration. If reflection had altered one of those statements, the
-- alias would be refused, as ClosedReflectedAsCrisp is. So for the
-- examples of the tree the reflected-term entry point declared what was
-- written: each family is a name, a composite of names, or a λ without
-- a binder annotation.
module ClosedSliceExistingStatements where

open import Foundations
open import FlatContext
  using (TypeContext; type-context-discrete; TypeFamily)
open import ClosedSliceShape using (ClosedShapeOver)
open import RelativeSliceShape using (RelativeShapeOver)
open import CaptureContext using (CrispUnitAt; unit-at-discrete)
open import CaptureReconstructionFixtures using (Carrier; z₀)
open import DependentDiagramFixtures
  using (Row; Col; row-discrete; col-discrete; step; Cell)
open import ClosedSliceExamples
  using (bool-set; bool-discrete; Family; ReindexedFamily; shaped; reshaped)
open import RelativeGenericExamples using (shaped-type-context)
open import ShapeReindexingExamples
  using (collapse; square-type; original; after-collapse; after-square)
open import AssemblyClientAPayloads using (sliceB; sliceC)
open import SurfaceAmbientFlags using (closed-under-flags)
open import Agda.Builtin.Bool using (Bool)

-- ClosedSliceExamples: the earlier head.
shaped-as-written : ClosedShapeOver Bool bool-set bool-discrete Family
shaped-as-written = shaped

reshaped-as-written :
  ClosedShapeOver Bool bool-set bool-discrete ReindexedFamily
reshaped-as-written = reshaped

-- RelativeGenericExamples.
shaped-type-context-as-written :
  RelativeShapeOver TypeContext type-context-discrete TypeFamily
shaped-type-context-as-written = shaped-type-context

-- ShapeReindexingExamples.
original-as-written : RelativeShapeOver Bool bool-discrete Family
original-as-written = original

after-collapse-as-written :
  RelativeShapeOver Bool bool-discrete (Family ∘ collapse)
after-collapse-as-written = after-collapse

after-square-as-written :
  RelativeShapeOver TypeContext type-context-discrete
    (TypeFamily ∘ square-type)
after-square-as-written = after-square

-- AssemblyClientAPayloads.
sliceB-as-written : RelativeShapeOver Row row-discrete Cell
sliceB-as-written = sliceB

sliceC-as-written : RelativeShapeOver Col col-discrete (Cell ∘ step)
sliceC-as-written = sliceC

-- SurfaceAmbientFlags: the one statement with a family written inline.
closed-under-flags-as-written :
  RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete
    (λ _ → Carrier z₀)
closed-under-flags-as-written = closed-under-flags
