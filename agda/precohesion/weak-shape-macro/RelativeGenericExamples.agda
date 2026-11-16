{-# OPTIONS --cohesion --without-K --flat-split #-}

module RelativeGenericExamples where

open import Foundations
open import FlatContext
open import RelativeSliceShape
open import DeclareClosedShape

-- This is one closed DECLARATION for the whole native crisp type context.
-- Its type is not ∀ A → ReflectionOf A. The declaration generates an axiom
-- instance of the contextual schema, not a construction of its semantics.
unquoteDecl shaped-type-context = declareClosedShape shaped-type-context
  (quoteTerm (RelativeShapeOver TypeContext type-context-discrete TypeFamily))

-- We may use the resulting family in a genuine native open crisp context.
Shape-in-type-context : (@♭ A : Set) → Set₁
Shape-in-type-context A = Output.family shaped-type-context (box A)

unit-in-type-context : (@♭ A : Set) → A → Shape-in-type-context A
unit-in-type-context A a =
  Output.family-unit shaped-type-context (box A) (lift a)

set-in-type-context : (@♭ A : Set) → IsSet (Shape-in-type-context A)
set-in-type-context A = Output.family-set shaped-type-context (box A)

-- The available recursion principle concerns the ENTIRE displayed family.
-- It does not make each Shape-in-type-context A the terminal-context
-- reflection of A. No pointwise reflection/elimination axiom is asserted.
whole-context-universal : SliceUniversal TypeContext TypeFamily
  (Output.Total shaped-type-context)
  (Output.projection shaped-type-context)
  (Output.unit shaped-type-context)
  (Output.unit-over shaped-type-context)
whole-context-universal = Output.universal shaped-type-context

module NativeUse (@♭ A : Set) where
  Result : Set₁
  Result = Shape-in-type-context A

  into-result : A → Result
  into-result = unit-in-type-context A

