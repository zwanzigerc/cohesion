{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Two closed slice declarations for the diagram step : Col → Row with the
-- family Cell: a choice of relative reflections that is independent of the
-- one the assembly library derives. Used by AssemblyClientA to exercise
-- ForPayloads and KernelFrom. fable-impl-11. Declarations: two shapes.
module AssemblyClientAPayloads where

open import Foundations
open import RelativeSliceShape
open import DeclareClosedShape using (declareClosedShape)
open import DependentDiagramFixtures
  using (Row; Col; row-discrete; col-discrete; step; Cell)

unquoteDecl sliceB = declareClosedShape sliceB
  (quoteTerm (RelativeShapeOver Row row-discrete Cell))

unquoteDecl sliceC = declareClosedShape sliceC
  (quoteTerm (RelativeShapeOver Col col-discrete (Cell ∘ step)))
