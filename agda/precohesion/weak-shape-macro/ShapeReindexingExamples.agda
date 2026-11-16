{-# OPTIONS --cohesion --without-K --flat-split #-}

module ShapeReindexingExamples where

open import Foundations
open import RelativeSliceShape
open import DeclareClosedShape
open import ShapeReindexing
open import FlatContext
import RelativeGenericExamples as Generic
open import ClosedSliceExamples using (Family; bool-discrete)
open import Agda.Builtin.Bool

-- A noninvertible substitution between discrete set contexts.
collapse : Bool → Bool
collapse _ = false

unquoteDecl original = declareClosedShape original
  (quoteTerm (RelativeShapeOver Bool bool-discrete Family))

unquoteDecl after-collapse = declareClosedShape after-collapse
  (quoteTerm (RelativeShapeOver Bool bool-discrete (Family ∘ collapse)))

module BooleanComparison = Comparison Bool Bool bool-discrete bool-discrete
  Family collapse original after-collapse

boolean-comparison : (b : Bool)
                   → Output.family after-collapse b
                   → Output.family original (collapse b)
boolean-comparison = BooleanComparison.comparison

boolean-comparison-on-unit : (b : Bool) (a : Family (collapse b))
  → boolean-comparison b (Output.family-unit after-collapse b a)
    ≡ Output.family-unit original (collapse b) a
boolean-comparison-on-unit = BooleanComparison.comparison-on-unit

-- A substitution in the higher native crisp TYPE context. No assumption
-- that the universe or this base is a homotopical set is needed.
square-type : TypeContext → TypeContext
square-type (box A) = box (A × A)

unquoteDecl after-square = declareClosedShape after-square
  (quoteTerm (RelativeShapeOver TypeContext type-context-discrete
    (TypeFamily ∘ square-type)))

module TypeComparison = Comparison TypeContext TypeContext
  type-context-discrete type-context-discrete TypeFamily square-type
  Generic.shaped-type-context after-square

type-context-comparison : (@♭ A : Set)
  → Output.family after-square (box A)
  → Generic.Shape-in-type-context (A × A)
type-context-comparison A = TypeComparison.comparison (box A)

type-context-comparison-on-unit : (@♭ A : Set) (a b : A)
  → type-context-comparison A
      (Output.family-unit after-square (box A) (lift (a , b)))
    ≡ Generic.unit-in-type-context (A × A) (a , b)
type-context-comparison-on-unit A a b =
  TypeComparison.comparison-on-unit (box A) (lift (a , b))

