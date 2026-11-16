{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The typed entry point for an explicitly written closed slice, in use.
-- Claude (Fable), 14 November 2026; fable-impl-21
-- (FABLE-C12-RECONCILIATION-REQUEST: the ordinary control, the named
-- family, and the constant checked at a statement written out natively).
--
-- WHAT IS DECLARED HERE. Five constants, each by ONE call of
-- declareClosedShapeTyped in the empty context: `ordinary`, `named`,
-- `under-flags`, `earlier-head` and `type-context`. Each is an axiom of
-- the closed-slice schema for the closed base and family that its line
-- shows. They are examples and are used by nothing else in the tree.
-- Every definition after a declaration is ordinary Agda, checked by the
-- compiler as usual: each `…-checked` is the constant at a statement that
-- is WRITTEN OUT in its type signature.
module ClosedSliceTypedExamples where

open import Foundations
open import FlatContext
  using (TypeContext; type-context-discrete; TypeFamily)
open import ClosedSliceShape using (ClosedShapeOver)
open import RelativeSliceShape
open import CaptureContext using (CrispUnitAt; unit-at-discrete)
open import ClosedSliceExamples using (bool-set; bool-discrete)
open import DeclareClosedShapeTyped
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Reflection
  using (withReconstructed; withNormalisation)

private
  One : Set
  One = CrispUnitAt lzero

------------------------------------------------------------------------
-- 1. The ordinary control. The family is written inline and its function
--    type has an ordinary binder; such a statement passes through
--    reflection unchanged, and the declaration is accepted.

unquoteDecl ordinary = declareClosedShapeTyped ordinary
  (RelativeShapeOver One unit-at-discrete (λ _ → ((x : ⊤) → ⊤)))

ordinary-checked :
  RelativeShapeOver One unit-at-discrete (λ _ → ((x : ⊤) → ⊤))
ordinary-checked = ordinary

------------------------------------------------------------------------
-- 2. A family with a CRISP function type, given by name. Reflection keeps
--    the name; the definition of the family is never read back from
--    syntax. The declaration is accepted, and the constant checks at the
--    family written out inline with its crisp binder: the two families
--    are equal by unfolding the name.

crisp-family : One → Set
crisp-family _ = (@♭ x : ⊤) → ⊤

unquoteDecl named = declareClosedShapeTyped named
  (RelativeShapeOver One unit-at-discrete crisp-family)

named-checked :
  RelativeShapeOver One unit-at-discrete (λ _ → ((@♭ x : ⊤) → ⊤))
named-checked = named

-- The output of the declared slice is about that family: its unit takes
-- a function of a crisp argument.
named-unit : (c : One) → ((@♭ x : ⊤) → ⊤) → Output.family named c
named-unit = Output.family-unit named

------------------------------------------------------------------------
-- 3. Under reflection flags set by the caller. The program fixes both
--    flags before its first primitive; in particular an enclosing
--    withNormalisation true does not unfold crisp-family before the
--    statement is quoted. (If it did, the crisp binder would come into
--    the reflected statement and be lost, and the native comparison
--    would refuse the declaration: a probe with the guard removed shows
--    exactly that, see CLOSED-SLICE-TYPED.txt.)

unquoteDecl under-flags =
  withReconstructed true (withNormalisation true
    (declareClosedShapeTyped under-flags
      (RelativeShapeOver One unit-at-discrete crisp-family)))

under-flags-checked :
  RelativeShapeOver One unit-at-discrete (λ _ → ((@♭ x : ⊤) → ⊤))
under-flags-checked = under-flags

------------------------------------------------------------------------
-- 4. The two supported heads. The earlier form ClosedShapeOver is
--    accepted as before, and so is a statement of an existing example
--    (RelativeGenericExamples), now without quoteTerm.

private
  constant : Bool → Set
  constant _ = ⊤

unquoteDecl earlier-head = declareClosedShapeTyped earlier-head
  (ClosedShapeOver Bool bool-set bool-discrete constant)

earlier-head-checked : ClosedShapeOver Bool bool-set bool-discrete (λ _ → ⊤)
earlier-head-checked = earlier-head

unquoteDecl type-context = declareClosedShapeTyped type-context
  (RelativeShapeOver TypeContext type-context-discrete TypeFamily)

type-context-checked :
  RelativeShapeOver TypeContext type-context-discrete TypeFamily
type-context-checked = type-context
