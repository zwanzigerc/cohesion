{-# OPTIONS --cohesion --without-K --flat-split #-}

module NestedShapeExamples where

open import Foundations
import CapturedShape as C
open import CaptureShape using (shape)
import NestedShapeFixtures as Earlier

module Example (@♭ A : Set) where
  nested : C.CapturedShape (C.Output.carrier (Earlier.First.shaped A))
  nested = shape

  nested-unit : C.Output.carrier (Earlier.First.shaped A)
              → C.Output.carrier nested
  nested-unit = C.Output.unit nested

  compound : C.CapturedShape
    (C.Output.carrier (Earlier.First.shaped A) × A)
  compound = shape

  compound-unit : C.Output.carrier (Earlier.First.shaped A) × A
                → C.Output.carrier compound
  compound-unit = C.Output.unit compound
