{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Import the earlier shape from another file before constructing a new one
-- whose source mentions its output. This avoids the rc3 local reconstruction
-- regression while retaining all capture/closure checks.
module NestedShapeFixtures where

open import Foundations
import CapturedShape as C
open import CaptureShape using (shape)

module First (@♭ A : Set) where
  shaped : C.CapturedShape A
  shaped = shape
