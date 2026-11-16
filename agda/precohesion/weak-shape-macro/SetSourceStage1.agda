{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE STAGED SET-SOURCE CLIENT, STAGE 1: the designated whole diagram,
-- its two payloads, their truncations, and the first shape of the kernel.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, section 11.3 b;
-- SET-SOURCE-PLAN-ASTRA-RELEASE-01).
--
-- The designated diagram is the WHOLE diagram of the index that
-- StagedDiagramClient reads from the dependent Bool/Code diagram: bases
-- Σ G B and Σ G C over the packed context G, the lifted map and the whole
-- family, at level 0. Nothing of it is written again: every datum below
-- is a field of that index.
--
-- DECLARATIONS OF THIS FILE: three, each a closed statement in the empty
-- context, entered by declareClosedShapeTyped with a named family.
--   MB, MC   the two ORIGINAL payloads, on the whole families. They are
--            inputs of the theorem, not among its 21 choices.
--   KO       choice 1 of 21: the shape of ♯ (O 0).
-- Nothing else is declared here. The truncated payloads and the kernel's
-- first module are DEFINED.
--
-- ORDINARY ASSUMPTIONS: those of SetSourceFoundation, by name. None is
-- declared here and none is hidden in a declaration: the three
-- statements mention only the index and the classifier.
module SetSourceStage1 where

open import Foundations
open import CaptureContext
  using (CrispUnitAt; unit-at-discrete; unpack-unit-at; Raise)
open import NativeSharp using (♯)
open import GlobalPrecohesion using (ShapeData)
open import ClosedBridge using (module Bridge)
open import RelativeSliceShape
open import DeclareClosedShapeTyped
open import ShapeElim using (module SigmaDiscrete)
open import TotalBridge using (Σ-set)
open import DecidableBase using (decidable-set)
open import DiagramMetadata
open import DiagramData using (Reindexed)
open import StagedDiagramClient using (index)
open import BaseClassifier using (O)
open import OrdinaryTruncation
open import TruncatedPayload using (module Truncate)
open import SetSourceFoundation public
import SetSourceKernelStatements as Statements

private
  module M = MetaField

ℓ₁ ℓ₂ : Level
ℓ₁ = lsuc lzero
ℓ₂ = lsuc ℓ₁

------------------------------------------------------------------------
-- 1. The whole diagram of the index. Definitions.

G : Set
G = M.G index

WB WC : Set
WB = Σ G (M.B index)
WC = Σ G (M.C index)

-- The discreteness witnesses are those of the assembly library
-- (DecidableRestriction.base-discrete), so that the payloads below are
-- accepted by DiagramAssembly.KernelFrom at every point.
dWB : Discrete WB
dWB = SigmaDiscrete.discrete (M.dG index) (M.dB index)

dWC : Discrete WC
dWC = SigmaDiscrete.discrete (M.dG index) (M.dC index)

WB-set : IsSet WB
WB-set = Σ-set (decidable-set (M.dec index)) (M.B-set index)

WC-set : IsSet WC
WC-set = Σ-set (decidable-set (M.dec index)) (M.C-set index)

wf : WC → WB
wf w = fst w , M.f index (fst w) (snd w)

WA : WB → Set
WA = M.A index

WA′ : WC → Set
WA′ = Reindexed (M.f index) (M.A index)

------------------------------------------------------------------------
-- 2. The two original payloads. DECLARED.

unquoteDecl MB = declareClosedShapeTyped MB (RelativeShapeOver WB dWB WA)

unquoteDecl MC = declareClosedShapeTyped MC (RelativeShapeOver WC dWC WA′)

------------------------------------------------------------------------
-- 3. Their truncations. DEFINED, on the carriers of MB and MC.
--
--    The implicit arguments are GIVEN, and the family of the second
--    payload is written WA ∘ wf, as ComparisonTransfer writes it. Then
--    the comparison of the kernel and the comparison of the accepted
--    transfer have the same payload terms, and SetSourceApplication
--    composes them without a costly conversion.

τ : SetTruncation lzero
τ = truncation₀

A₀ : WB → Set
A₀ b = SetTruncation.τ₀ τ (WA b)

A₀-set : (b : WB) → IsSet (A₀ b)
A₀-set b = SetTruncation.τ₀-set τ

K₀ : RelativeShapeOver WB dWB A₀
K₀ = Truncate.truncate-payload τ fe₀₀ {WB} {dWB} {WA} MB

K₀′ : RelativeShapeOver WC dWC (A₀ ∘ wf)
K₀′ = Truncate.truncate-payload τ fe₀₀ {WC} {dWC} {WA ∘ wf} MC

------------------------------------------------------------------------
-- 4. Choice 1 of 21: the shape of ♯ (O 0), a type of level 1. DECLARED,
--    then turned into terminal shape data by the closed bridge.

T-O : Set₁
T-O = ♯ (O lzero)

F-O : CrispUnitAt ℓ₁ → Set₁
F-O = unpack-unit-at (Raise ℓ₁ T-O)

unquoteDecl KO = declareClosedShapeTyped KO
  (RelativeShapeOver (CrispUnitAt ℓ₁) unit-at-discrete F-O)

sO : ShapeData T-O
sO = Bridge.data-of fe₁₁ T-O KO

------------------------------------------------------------------------
-- 5. The kernel's first module, at these closed data. DEFINED: a module
--    application, which declares nothing.

module K1 = Statements.Kernel fe₀₀ fe₁₁ fe₂₂ fe₀₁ fe₁₂ pe₀ pe₁
  Q₁ E₁ effective₁ Q₂ E₂
  WB WC dWB dWC WB-set WC-set A₀ A₀-set wf K₀ K₀′ sO
