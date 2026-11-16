{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The input contract of the REFLECTED-TERM entry point
-- DeclareClosedShape.declareClosedShape, stated as checked facts.
-- Claude (Fable), 14 November 2026; fable-impl-21
-- (FABLE-C12-RECONCILIATION-REQUEST; the receipts C12Inline,
-- C12AsOrdinary and C12NamedAsCrisp of the reconciliation probes, as
-- cases of the suite; ClosedReflectedAsCrisp is C12AsCrisp).
--
-- That entry point is unchanged. It declares what the TERM it is given
-- denotes after elaboration. Reflected syntax has no cohesion annotation,
-- so:
--   1. a crisp function type written INLINE in the quoted statement is
--      declared as an ordinary one. `inline` below is accepted, and its
--      type is the statement with (x : ⊤) → ⊤. This is the behaviour that
--      the independent audit found; it is recorded here, not endorsed as
--      a way to write a statement.
--   2. a family given BY NAME is kept. `by-name` checks at the family
--      written inline with the crisp binder.
-- A user who writes a statement by hand uses
-- DeclareClosedShapeTyped.declareClosedShapeTyped, which refuses case 1
-- (ClosedTypedInlineCrisp). With the reflected-term entry point, a typed
-- alias such as `inline-is-ordinary` is the check, and it is the caller's
-- to write.
--
-- WHAT IS DECLARED HERE. Two constants, `inline` and `by-name`, each an
-- axiom of the closed-slice schema for a closed base and family. They are
-- examples and are used only by the case ClosedReflectedAsCrisp.
module ClosedSliceReflectedContract where

open import Foundations
open import RelativeSliceShape
open import CaptureContext using (CrispUnitAt; unit-at-discrete)
open import DeclareClosedShape
open import ClosedSliceTypedExamples using (crisp-family)

private
  One : Set
  One = CrispUnitAt lzero

-- 1. Written with a crisp binder; declared with an ordinary one.
unquoteDecl inline = declareClosedShape inline
  (quoteTerm (RelativeShapeOver One unit-at-discrete
    (λ _ → ((@♭ x : ⊤) → ⊤))))

inline-is-ordinary :
  RelativeShapeOver One unit-at-discrete (λ _ → ((x : ⊤) → ⊤))
inline-is-ordinary = inline

-- 2. The same family under a name.
unquoteDecl by-name = declareClosedShape by-name
  (quoteTerm (RelativeShapeOver One unit-at-discrete crisp-family))

by-name-checked :
  RelativeShapeOver One unit-at-discrete (λ _ → ((@♭ x : ⊤) → ⊤))
by-name-checked = by-name
