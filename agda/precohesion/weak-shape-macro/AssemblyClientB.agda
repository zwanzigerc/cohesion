{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Target-style client B of the assembly library: a diagram in an OPEN
-- dependent crisp context. Claude (Fable), 13 November 2026; fable-impl-11.
--
-- The user's module has the context  (b : Bool) (v : Code b)  and the
-- diagram of DependentDiagramFixtures:
--     baseMap b v : BaseC b v → BaseB b v,   Fam b v : BaseB b v → Set.
-- The local bases are discrete sets for which no decision procedure is
-- supplied; the fibres of Fam are arbitrary. Only the packed context has
-- decidable equality (from bool-dec and code-dec).
--
-- Parts marked GENERATED are what the frontend of steps S2/S3 is to
-- produce; here they are TYPED IN, in the form a reflection macro can
-- emit (unpacking combinators, no pattern-matching clauses). There is no
-- generator in this snapshot, and this file is not the direct in-module
-- endpoint: the user's diagram is given as closed curried families, and
-- the two captures of the whole total sources are made at top level.
-- What is new against fable-impl-10 (ReindexingAcceptanceB): no source
-- identifications, no packed point written by the user (the generated
-- helper `point` builds it), one generated name. Results about the
-- DEFAULT (sealed) outputs are stated in the terms of the user's module;
-- results about the raw outputs are stated in the library's terms.
--
-- Three things are exercised that the plan audits asked for:
--   Assembled   the boundary of the library's opaque payload copies:
--               reflections of the whole diagram from the ORIGINAL
--               supplied payloads, KernelFrom, the public GLOBAL Kernel
--   Open        the LOCAL native conclusion at the point, from Kernel and
--               from ordinary evidence about the original global
--               comparison (local-from-original)
--   Interop     fresh captures of the local total sources, FromCapture,
--               ForPayloads: the conclusion for their reflections from
--               the same Kernel
--
-- Declarations of this file: four shapes. Two are the generated captures
-- of the whole total sources. Two are FRESH captures of the local total
-- sources, made in the user's open context before function
-- extensionality is introduced; they feed ForPayloads through
-- DiagramAssembly.FromCapture (module Interop).
module AssemblyClientB where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import CaptureContext
  using (CrispΣ; pair; CrispUnitAt; end-at; telescope-discrete;
         unpack; unpack-dependent)
open import CaptureUnpack using (unpack-crisp; unpack-end-crisp)
open import ShapeChoice using (FunExtAt)
open import ClosedBridge using (closed-bridge)
open import TotalConverse using (module Converse)
open import DecidableBase using (DecEq; context-dec; unit-at-dec)
open import DecidableTelescope using (dependent-context-dec)
open import BoolDecidable using (bool-dec)
open import DependentContextFixtures using (Code; code-dec)
open import DependentDiagramFixtures
open import ReindexingAssembly using (module TotalForm)
open import DiagramAssembly using (module FromCapture)
open import DiagramBundle

------------------------------------------------------------------------
-- GENERATED: the packed context, its decision procedure, the point.

Ctx : Set
Ctx = CrispΣ Bool (λ b → CrispΣ (Code b) (λ _ → CrispUnitAt lzero))

ctx-dec : DecEq Ctx
ctx-dec = dependent-context-dec bool-dec
  (λ b → context-dec (code-dec b) unit-at-dec)

-- The curried point: the user passes native variables.
point : (@♭ b : Bool) (@♭ v : Code b) → Ctx
point b v = pair b (pair v end-at)

-- GENERATED: the packed diagram and its evidence, in combinator form.

B̃ : Ctx → Set
B̃ = unpack (λ b t → unpack (λ v _ → BaseB b v) t)

C̃ : Ctx → Set
C̃ = unpack (λ b t → unpack (λ v _ → BaseC b v) t)

f̃ : (g : Ctx) → C̃ g → B̃ g
f̃ = unpack-dependent (λ g → C̃ g → B̃ g) (λ b t →
    unpack-crisp (λ t′ → C̃ (pair b t′) → B̃ (pair b t′)) (λ v u →
    unpack-end-crisp (λ u′ → C̃ (pair b (pair v u′)) → B̃ (pair b (pair v u′)))
      (baseMap b v) u) t)

Ã : Σ Ctx B̃ → Set
Ã w = unpack-dependent (λ g → B̃ g → Set) (λ b t →
      unpack-crisp (λ t′ → B̃ (pair b t′) → Set) (λ v u →
      unpack-end-crisp (λ u′ → B̃ (pair b (pair v u′)) → Set)
        (Fam b v) u) t) (fst w) (snd w)

dB̃ : (@♭ g : Ctx) → Discrete (B̃ g)
dB̃ = unpack-crisp (λ g → Discrete (B̃ g)) (λ b t →
     unpack-crisp (λ t′ → Discrete (B̃ (pair b t′))) (λ v u →
     unpack-end-crisp (λ u′ → Discrete (B̃ (pair b (pair v u′))))
       (baseB-discrete b v) u) t)

B̃-set : (g : Ctx) → IsSet (B̃ g)
B̃-set = unpack-dependent (λ g → IsSet (B̃ g)) (λ b t →
        unpack-crisp (λ t′ → IsSet (B̃ (pair b t′))) (λ v u →
        unpack-end-crisp (λ u′ → IsSet (B̃ (pair b (pair v u′))))
          (baseB-set b v) u) t)

dC̃ : (@♭ g : Ctx) → Discrete (C̃ g)
dC̃ = unpack-crisp (λ g → Discrete (C̃ g)) (λ b t →
     unpack-crisp (λ t′ → Discrete (C̃ (pair b t′))) (λ v u →
     unpack-end-crisp (λ u′ → Discrete (C̃ (pair b (pair v u′))))
       (baseC-discrete b v) u) t)

C̃-set : (g : Ctx) → IsSet (C̃ g)
C̃-set = unpack-dependent (λ g → IsSet (C̃ g)) (λ b t →
        unpack-crisp (λ t′ → IsSet (C̃ (pair b t′))) (λ v u →
        unpack-end-crisp (λ u′ → IsSet (C̃ (pair b (pair v u′))))
          (baseC-set b v) u) t)

-- GENERATED: the two captures, of the WHOLE total sources, in the empty
-- context, and the one value.

whole-B : CapturedShape (Σ (Σ Ctx B̃) Ã)
whole-B = shape

whole-C : CapturedShape (Σ (Σ Ctx C̃) (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w))))
whole-C = shape

diagram : OpenDiagram lzero
diagram = open-diagram Ctx telescope-discrete ctx-dec B̃ C̃
  dB̃ B̃-set dC̃ C̃-set f̃ Ã
  (C.Output.whole-context whole-B) (C.Output.whole-context whole-C)

------------------------------------------------------------------------
-- USER: two fresh captures of the local total sources, in the open
-- context, for module Interop below. Not needed for module Open.

module Fresh (@♭ b : Bool) (@♭ v : Code b) where

  captured-B : CapturedShape (Σ (BaseB b v) (Fam b v))
  captured-B = shape

  captured-C : CapturedShape (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  captured-C = shape

------------------------------------------------------------------------
-- USER: the library applied to the one generated name. Everything here
-- is about the WHOLE diagram over the packed context; no point yet.

module Assembled (@♭ fe : FunExtAt lzero) where

  module D = AssembleOpen fe diagram

  -- The whole interface. Kernel is the total-form statement about the
  -- public module Whole: the comparison of the GLOBAL diagram
  --   Σ Ctx C̃ → Σ Ctx B̃.
  kernel-is : D.Kernel ≡ D.Whole.TotalComparisonIsEquivalence
  kernel-is = refl

  -- THE BOUNDARY OF THE OPAQUE PAYLOADS, as in AssemblyClientA: the
  -- reflections of the whole diagram derived from the ORIGINAL supplied
  -- payloads, over the library's own public base witnesses, and
  -- KernelFrom. Ordinary evidence about the original global comparison
  -- gives the public Kernel.
  originalB : RelativeShapeOver (Σ Ctx B̃) D.wholeB-discrete Ã
  originalB = Converse.relative fe {dΓ = D.wholeB-discrete} D.wholeB-set
    (closed-bridge fe (Σ (Σ Ctx B̃) Ã) (OpenField.KB diagram))

  originalC : RelativeShapeOver (Σ Ctx C̃) D.wholeC-discrete
                (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w)))
  originalC = Converse.relative fe {dΓ = D.wholeC-discrete} D.wholeC-set
    (closed-bridge fe
      (Σ (Σ Ctx C̃) (Ã ∘ (λ w → fst w , f̃ (fst w) (snd w))))
      (OpenField.KC diagram))

  module Original = D.KernelFrom originalB originalC

  kernel-from-original : Original.Supplied.TotalComparisonIsEquivalence
                       → D.Kernel
  kernel-from-original = Original.kernel

------------------------------------------------------------------------
-- USER: the open module. One generated name, one generated helper.

module Open (@♭ fe : FunExtAt lzero) (@♭ b : Bool) (@♭ v : Code b) where

  open Assembled fe public using (module D; module Original)
  module Here = D.At (point b v)

  -- At the point of the context the fields ARE the user's data.
  same-baseB : OpenField.B diagram (point b v) ≡ BaseB b v
  same-baseB = refl

  same-baseC : OpenField.C diagram (point b v) ≡ BaseC b v
  same-baseC = refl

  same-map : OpenField.f diagram (point b v) ≡ baseMap b v
  same-map = refl

  same-family : (λ r → OpenField.A diagram (point b v , r)) ≡ Fam b v
  same-family = refl

  -- Default outputs. The canonical comparison of the local diagram,
  -- stated in the terms of this module, with its unit law.
  module Native = TotalForm (BaseB b v) (BaseC b v)
    (baseB-discrete b v) (baseC-discrete b v) (Fam b v) (baseMap b v)
    Here.reflB Here.reflC

  result : D.Kernel → (k : BaseC b v) → IsEquiv (Native.comparison k)
  result = Here.from-kernel

  unit-law : (k : BaseC b v) (a : Fam b v (baseMap b v k))
           → Native.comparison k (Output.family-unit Here.reflC k a)
             ≡ Output.family-unit Here.reflB (baseMap b v k) a
  unit-law = Native.comparison-on-unit

  -- Raw outputs: the whole reflections restricted to the fibre of the
  -- context over the point. Results about them are stated in the
  -- library's own terms (Here.Raw). Restated in the terms of this module
  -- they are a second spelling of large transparent terms, and the check
  -- does not finish (diagnostics/payload-atoms); the default outputs are
  -- there for that.
  raw-result : D.Kernel → Here.Raw.ComparisonIsEquivalence
  raw-result = Here.raw-from-kernel

  -- The square that relates the local comparison to the whole one, and
  -- the canonical bridges between raw and default outputs with their
  -- unit laws, are used under the library's names:
  --   Here.square, Here.BridgeB.forward, Here.BridgeC.forward-on-unit, ...
  -- For instance the bridge on the C side has this native type.
  to-default : (k : BaseC b v)
             → Output.family Here.raw-reflC k → Output.family Here.reflC k
  to-default = Here.BridgeC.forward

  default-is-raw : Here.reflC ≡ Here.raw-reflC
  default-is-raw = Here.reflC-path

  -- The square of the raw local comparison with the bridges is
  -- Here.Sealing.natural, used under that name. Written out with an
  -- explicit signature it is not checked within the heap limit, in this
  -- client or in the library itself (diagnostics/open-naturality): at a
  -- point the raw outputs are large transparent terms. The closed square
  -- displayed in AssemblyClientA (commute) is checked with its signature;
  -- that is a fact about that square, not the absence of resource limits
  -- in the closed form (wording corrected after fable-impl-11,
  -- M11-DOCUMENTATION-CORRECTIONS-01 item 3).
  commute = Here.Sealing.natural

  -- What Sealing.pull is: the B-side bridge in each fibre.
  pull-is = Here.pull-is

  -- From ORDINARY evidence about the ORIGINAL GLOBAL comparison to the
  -- LOCAL canonical conclusion at the current point, natively stated.
  local-from-original : Original.Supplied.TotalComparisonIsEquivalence
                      → (k : BaseC b v) → IsEquiv (Native.comparison k)
  local-from-original e = Here.from-kernel (Original.kernel e)

------------------------------------------------------------------------
-- USER: interoperation with the fresh captures.

module Interop (@♭ fe : FunExtAt lzero) (@♭ b : Bool) (@♭ v : Code b) where

  open Open fe b v using (module D; module Here)

  -- From each fresh capture, the relative reflection over the local base.
  -- The decision procedure is that of the packed context only.
  module FB = FromCapture fe (baseB-discrete b v) (baseB-set b v)
    (Fresh.captured-B b v) ctx-dec
  module FC = FromCapture fe (baseC-discrete b v) (baseC-set b v)
    (Fresh.captured-C b v) ctx-dec

  -- The raw reflections have the carriers and the units of the captures.
  same-carrier : Output.Total FC.raw-reflection
               ≡ C.Output.carrier (Fresh.captured-C b v)
  same-carrier = refl

  same-unit : (x : Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
            → Output.unit FC.raw-reflection x
              ≡ C.Output.unit (Fresh.captured-C b v) x
  same-unit x = refl

  -- The conclusion for the reflections of the fresh captures, from the
  -- same Kernel: for the raw ones in the library's terms ...
  module RawTransfer = Here.ForPayloads FB.raw-reflection FC.raw-reflection

  raw-fresh-result : D.Kernel → RawTransfer.Chosen.ComparisonIsEquivalence
  raw-fresh-result = RawTransfer.from-kernel′

  -- ... and for the default (sealed) ones in the terms of this module,
  -- with the canonical comparison and its unit law.
  module Transfer = Here.ForPayloads FB.reflection FC.reflection

  module NativeFresh = TotalForm (BaseB b v) (BaseC b v)
    (baseB-discrete b v) (baseC-discrete b v) (Fam b v) (baseMap b v)
    FB.reflection FC.reflection

  fresh-result : D.Kernel → (k : BaseC b v) → IsEquiv (NativeFresh.comparison k)
  fresh-result = Transfer.from-kernel′

  fresh-unit-law : (k : BaseC b v) (a : Fam b v (baseMap b v k))
                 → NativeFresh.comparison k (Output.family-unit FC.reflection k a)
                   ≡ Output.family-unit FB.reflection (baseMap b v k) a
  fresh-unit-law = NativeFresh.comparison-on-unit
