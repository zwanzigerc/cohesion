{-# OPTIONS --cohesion --without-K --flat-split #-}

module ShapeChoiceExamples where

open import Foundations
open import CaptureShape using (shape)
import CapturedShape as C
open import ShapeChoice

-- Two independent invocations, with the same source and entire context.
module Calls (@♭ A : Set) where
  first : C.CapturedShape A
  first = shape

  second : C.CapturedShape A
  second = shape

-- Keep the proof hypothesis outside the captured input telescope. It is
-- used to prove choice independence, not to create another shape instance.
module Agreement (@♭ fe : FunExtAt (lsuc lzero)) (@♭ A : Set) where
  module E = FiberChoice fe
    (C.Output.whole-context (Calls.first A))
    (C.Output.whole-context (Calls.second A))

  forward : C.Output.carrier (Calls.first A) → C.Output.carrier (Calls.second A)
  forward = E.forward (C.Output.point (Calls.first A))

  backward : C.Output.carrier (Calls.second A) → C.Output.carrier (Calls.first A)
  backward = E.backward (C.Output.point (Calls.first A))

  forward-is-equiv : IsEquiv forward
  forward-is-equiv = E.forward-is-equiv (C.Output.point (Calls.first A))

  backward-forward : (x : C.Output.carrier (Calls.first A))
                   → backward (forward x) ≡ x
  backward-forward = E.backward-forward (C.Output.point (Calls.first A))

  forward-backward : (y : C.Output.carrier (Calls.second A))
                   → forward (backward y) ≡ y
  forward-backward = E.forward-backward (C.Output.point (Calls.first A))

  forward-on-unit : (a : A)
                  → forward (C.Output.unit (Calls.first A) a)
                    ≡ C.Output.unit (Calls.second A) a
  forward-on-unit a = E.forward-on-unit (C.Output.point (Calls.first A))
    (C.Output.source-embed (Calls.first A) a)
