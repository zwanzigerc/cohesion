{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Target-style client of the DIRECT GENERATOR. Claude (Fable),
-- 13 November 2026; step S3b, after fable-impl-13.
--
-- The diagram is stated natively INSIDE the open context
--   (b : Bool) (v : Code b)
-- and ONE declaration there generates the bundle: the packed context, its
-- decision procedure, the packed diagram and evidence, the two captures
-- and the presentations. Nothing that AssemblyClientDirect has under
-- GENERATED is typed in here: no packed context, no eliminator, no packed
-- map or family, no point, no capture, no presentation, no At.
--
-- The fixtures are those of AssemblyClientB and AssemblyClientDirect: the
-- local bases have no decision procedure supplied, Fam has arbitrary
-- fibres, and the conclusion is CONDITIONAL on Kernel, an ordinary
-- hypothesis about the WHOLE diagram.
--
-- Declarations of this file: two shapes, requested by the one generator
-- call in the open context (shape-count below). They are contextual
-- choices of arity two.
module AssemblyClientGenerated where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureContext
  using (CrispΣ; pair; CrispUnitAt; end-at; telescope-discrete)
open import ShapeChoice using (FunExtAt)
open import TotalConverse using (module Converse)
open import BoolDecidable using (bool-dec)
open import DependentContextFixtures using (Code; code-dec)
open import DependentDiagramFixtures
open import DiagramBundle
open import DeclareCapturedDiagram
open import DiagramInventory using (shape-axioms)

module Local (@♭ b : Bool) (@♭ v : Code b) where

  ----------------------------------------------------------------------
  -- USER: the diagram, natively, once. One decision procedure for the
  -- type of each variable of the context, oldest first; the second one
  -- mentions the first variable.

  unquoteDecl cells =
    declareCapturedDiagram cells (bool-dec ∷ code-dec b ∷ [])
      (baseB-discrete b v) (baseB-set b v)
      (baseC-discrete b v) (baseC-set b v)
      (baseMap b v) (Fam b v)

  ----------------------------------------------------------------------
  -- What was generated, read off the one name. None of this is needed to
  -- use the bundle; it is checked here to show what the name contains.

  private
    module F = CapturedField

  -- The packed context is the context a capture packs here, and the
  -- stored point is the current one.
  context-is : F.G cells
             ≡ CrispΣ Bool (λ b′ → CrispΣ (Code b′) (λ _ → CrispUnitAt lzero))
  context-is = refl

  point-is : F.point cells ≡ pair b (pair v end-at)
  point-is = refl

  -- The packed data at the stored point are the native expressions: the
  -- bases, the map, the family, the evidence.
  base-B : F.B cells (F.point cells) ≡ BaseB b v
  base-B = refl

  base-C : F.C cells (F.point cells) ≡ BaseC b v
  base-C = refl

  map-here : F.f cells (F.point cells) ≡ baseMap b v
  map-here = refl

  family-here : FibreAt (F.A cells) (F.point cells) ≡ Fam b v
  family-here = refl

  evidence-B : F.dB cells (F.point cells) ≡ baseB-discrete b v
  evidence-B = refl

  evidence-C : F.dC cells (F.point cells) ≡ baseC-discrete b v
  evidence-C = refl

  sets-B : F.B-set cells (F.point cells) ≡ baseB-set b v
  sets-B = refl

  sets-C : F.C-set cells (F.point cells) ≡ baseC-set b v
  sets-C = refl

  source-B : F.TB cells (F.point cells) ≡ Σ (BaseB b v) (Fam b v)
  source-B = refl

  source-C : F.TC cells (F.point cells)
           ≡ Σ (BaseC b v) (λ k → Fam b v (baseMap b v k))
  source-C = refl

  -- The two captures, as the library reads them off the bundle.
  captured-B : CapturedShape (Σ (BaseB b v) (Fam b v))
  captured-B = F.localB cells

  captured-C : CapturedShape (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  captured-C = F.localC cells

  -- They pack this context at this point, with the source maps that
  -- every capture has.
  wrapper-context : C.Output.context captured-B ≡ F.G cells
  wrapper-context = refl

  wrapper-point : C.Output.point captured-C ≡ pair b (pair v end-at)
  wrapper-point = refl

  -- The call requested two shapes: the heads of the two payloads are two
  -- distinct axioms.
  shape-count : Nat
  shape-count = shape-axioms [] (quote captured-B ∷ quote captured-C ∷ [])

  two-shapes : shape-count ≡ 2
  two-shapes = refl

  ----------------------------------------------------------------------
  -- USER: the library applied to the one generated name, after function
  -- extensionality. No point, no At.

  module WithFE (@♭ fe : FunExtAt lzero) where

    module D = AssembleCaptured fe cells

    -- The canonical comparison of the local diagram, for the reflections
    -- of the two captures, natively typed, and its unit law.
    comparison : (k : BaseC b v)
               → Output.family D.reflC k → Output.family D.reflB (baseMap b v k)
    comparison = D.Diagram.comparison

    unit-law : (k : BaseC b v) (a : Fam b v (baseMap b v k))
             → comparison k (Output.family-unit D.reflC k a)
               ≡ Output.family-unit D.reflB (baseMap b v k) a
    unit-law = D.Diagram.comparison-on-unit

    -- The conclusion, from the kernel statement about the WHOLE diagram.
    -- kernel is an ordinary argument.
    result : D.Kernel → (k : BaseC b v) → IsEquiv (comparison k)
    result = D.from-kernel

    kernel-is : D.Kernel ≡ D.Whole.TotalComparisonIsEquivalence
    kernel-is = refl

    -- The raw reflections have the captures' own total carriers and
    -- units; the default ones are their sealed copies.
    raw-carrier : Output.Total D.CaptureB.raw-reflection ≡ C.Output.carrier captured-B
    raw-carrier = refl

    raw-unit : Output.unit D.CaptureB.raw-reflection ≡ C.Output.unit captured-B
    raw-unit = refl

    default-is-raw : D.reflB ≡ D.CaptureB.raw-reflection
    default-is-raw = D.CaptureB.reflection-path

    raw-result : D.Kernel → D.Here.Raw.ComparisonIsEquivalence
    raw-result = D.Here.raw-from-kernel

    -- The boundary of the opaque copies, as in AssemblyClientDirect:
    -- whole reflections derived from the TRANSPARENT derivedB, derivedC,
    -- with the core's public base witnesses; KernelFrom carries ordinary
    -- evidence about their comparison to Kernel and on to the local
    -- conclusion. The whole base and family are named through the bundle.
    originalB : RelativeShapeOver (Σ (F.G cells) (F.B cells)) D.wholeB-discrete
                  (F.A cells)
    originalB = Converse.relative fe {dΓ = D.wholeB-discrete} D.wholeB-set
      D.derivedB

    originalC : RelativeShapeOver (Σ (F.G cells) (F.C cells)) D.wholeC-discrete
                  (Reindexed (F.f cells) (F.A cells))
    originalC = Converse.relative fe {dΓ = D.wholeC-discrete} D.wholeC-set
      D.derivedC

    module Original = D.KernelFrom originalB originalC

    kernel-from-original : Original.Supplied.TotalComparisonIsEquivalence
                         → D.Kernel
    kernel-from-original = Original.kernel

    local-from-original : Original.Supplied.TotalComparisonIsEquivalence
                        → (k : BaseC b v) → IsEquiv (comparison k)
    local-from-original e = result (Original.kernel e)

    whole-carrier : Output.Total originalB
                  ≡ Output.Total (C.Output.whole-context captured-B)
    whole-carrier = refl
