{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The remaining exported reflection programs under reflection flags set by
-- an ENCLOSING caller. fable-impl-03; HANDOFF-06 item 1 and
-- FRONTEND-M2-AUDIT-01 R4. (capture and declareShape: CaptureAmbientFlags.)
--
-- Each exported program fixes both flags before its first primitive, so
-- every declaration below is accepted. The crisp context of `Hypothesis`
-- has the over-applied projection-like form on which Agda 2.9.0-rc3 aborts
-- when a primitive runs with parameter reconstruction; in fable-impl-02
-- `eliminate` and `checkCrispContext` inherited the caller's flags.
module SurfaceAmbientFlags where

open import Foundations
open import CaptureContext
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeElim
open import CaptureCrispCheck using (checkCrispContext)
open import DeclareClosedShape
open import RelativeSliceShape using (RelativeShapeOver)
open import GlobalDeclare using (declareProduct; module ProductStatement)
open import GlobalDeclareExamples using (K₁; K₂; K₁₂)
open import CaptureReconstructionFixtures
open import ClosedSliceExamples using (bool-set; bool-discrete)
open import Agda.Builtin.Reflection
  using (Term; TC; withReconstructed; withNormalisation; bindTC; unify; con)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.List using ([])

macro
  elim-reconstructed : Term → Term → Term → TC ⊤
  elim-reconstructed s d hole = withReconstructed true (eliminate s d hole)

  elim-both : Term → Term → Term → TC ⊤
  elim-both s d hole =
    withReconstructed true (withNormalisation true (eliminate s d hole))

  crisp-reconstructed : Term → TC ⊤
  crisp-reconstructed hole = withReconstructed true
    (bindTC checkCrispContext λ _ → unify hole (con (quote tt) []))

module Hypothesis
  (@♭ k : Packed ⊤) (@♭ x : Carrier k) (@♭ e : short k x ≡ short k x) where

  s : CapturedShape Bool
  s = shape

  into-bool : ShapeElim s (λ b → b)
  into-bool = elim-reconstructed bool-set bool-discrete

  again : ShapeElim s (λ b → b)
  again = elim-both bool-set bool-discrete

  computes : (b : Bool) → ShapeElim.map into-bool (C.Output.unit s b) ≡ b
  computes = ShapeElim.map-unit into-bool

  checked : ⊤
  checked = crisp-reconstructed

-- Closed declarations under the caller's flags.
unquoteDecl closed-under-flags =
  withReconstructed true (withNormalisation true
    (declareClosedShape closed-under-flags
      (quoteTerm (RelativeShapeOver (CrispUnitAt lzero) unit-at-discrete
        (λ _ → Carrier z₀)))))

unquoteDecl product-under-flags =
  withReconstructed true (declareProduct product-under-flags K₁ K₂ K₁₂)

its-type : ProductStatement.ProductAxiom K₁ K₂ K₁₂
its-type = product-under-flags
