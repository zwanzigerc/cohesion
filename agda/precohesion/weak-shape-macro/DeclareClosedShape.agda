{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Trusted axiom-schema frontend for an explicitly written closed family.
-- It only generates a ClosedShapeOver or RelativeShapeOver datum for a
-- closed native family. It never declares a uniform Shape function. All
-- ordinary native Agda proofs after this declaration use the usual kernel.
--
-- fable-impl-03 (FRONTEND-M2-AUDIT-01.txt R1, HANDOFF-06 item 1). In
-- fable-impl-02 this module exported two helpers, declareTypeClosed and
-- declareChecked. Neither checked the context, and `inContext []` restores
-- the context of the calling declaration; called inside a module with a
-- crisp parameter they declared a shape datum abstracted over that
-- parameter (frontend-m2-review-probes/M2ExportedClosedHelpers.agda).
--
-- The module exports ONE declaring entry point, declareClosedShape. Before
-- anything is declared it
--   * fixes both reflection flags (`guarded`);
--   * requires the context of the calling declaration (inContext []
--     getContext) and the current context to be empty;
--   * requires the statement to be an application of ClosedShapeOver or
--     RelativeShapeOver, and checks it in the empty context.
-- fable-impl-04 (FRONTEND-M3-AUDIT-01 section 1): in fable-impl-03 the
-- declaring primitive sat in a private leaf function that made no check of
-- its own, and the comment here claimed more than that. Now `declare` is
-- the only definition of this module that contains a declaring primitive,
-- and the checks are made in that same definition before the primitive is
-- reached; the helper functions only succeed or fail. `private` remains a
-- boundary of the source interface, not of reflection: a program that
-- copies the body of `declare` and edits it is a program that calls
-- declarePostulate itself, and nothing here speaks for it
-- (FABLE-REVIEW-03.txt, sections 1.3 and 3).
module DeclareClosedShape where

open import ClosedSliceShape
open import RelativeSliceShape using (RelativeShapeOver)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection as R using (Name; Term; TC; Telescope)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Unit using (⊤; tt)

private
  open-context : TC ⊤
  open-context = R.typeError
    (R.strErr "Closed shape declarations cannot depend on native module or local parameters. Package the intended object context as a closed native base and family." ∷ [])

  wrong-head : TC ⊤
  wrong-head = R.typeError
    (R.strErr "Expected a ClosedShapeOver or RelativeShapeOver type." ∷ [])

  -- Checks only: these two functions declare nothing.
  both-empty : Telescope → Telescope → TC ⊤
  both-empty [] [] = R.returnTC tt
  both-empty _ _ = open-context

  shape-head : Term → TC ⊤
  shape-head (R.def (quote ClosedShapeOver) _) = R.returnTC tt
  shape-head (R.def (quote RelativeShapeOver) _) = R.returnTC tt
  shape-head _ = wrong-head

  -- The only definition of this module that contains a declaring
  -- primitive. Flags, both contexts and the head are checked here, in this
  -- order, before declarePostulate is reached.
  declare : Name → Term → TC ⊤
  declare n t = guarded (
    R.bindTC (R.inContext [] R.getContext) λ calling →
    R.bindTC R.getContext λ current →
    R.bindTC (both-empty calling current) λ _ →
    R.bindTC (shape-head t) λ _ →
    R.bindTC (R.inferType t) λ sort →
    R.bindTC (R.checkType t sort) λ checked →
    R.declarePostulate
      (R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω)) n)
      checked)

-- Use: unquoteDecl k = declareClosedShape k (quoteTerm (ClosedShapeOver ...))
declareClosedShape : Name → Term → TC ⊤
declareClosedShape = declare
