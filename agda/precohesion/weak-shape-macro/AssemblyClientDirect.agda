{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Target-style client of the DIRECT in-module route. Claude (Fable),
-- 13 November 2026; step S3a, after fable-impl-12.
--
-- The diagram is stated natively INSIDE the open context
--   (b : Bool) (v : Code b)
-- and the two captures are made there, of the two local total sources.
-- No closed shape of a whole total exists in this file, and the user
-- writes no packed context, no packed map, no point and no At.
--
-- Parts marked GENERATED are what the frontend of step S3b is to produce;
-- here they are TYPED IN, in the form checked by the probe
-- diagnostics/direct-route/EliminatorForm: per telescope the packed
-- context, its decision procedure, the curried point and two
-- eliminators; after that every datum is an eliminator applied to a
-- motive and a curried leaf. There is no generator in this snapshot.
-- Parts marked USER are what a user writes.
--
-- The fixtures are those of AssemblyClientB: the local bases have no
-- decision procedure, Fam has arbitrary fibres, and the conclusion is
-- CONDITIONAL on Kernel, an ordinary hypothesis about the WHOLE diagram.
--
-- Declarations of this file: two shapes, the two captures in the open
-- context. They are contextual choices of arity two.
module AssemblyClientDirect where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import CaptureContext
  using (CrispΣ; pair; CrispUnitAt; end-at; telescope-discrete;
         unpack-dependent; raise; lower; raise-lower)
open import CaptureUnpack using (unpack-crisp; unpack-end-crisp)
open import ShapeChoice using (FunExtAt)
open import TotalConverse using (module Converse)
open import DecidableBase using (DecEq; context-dec; unit-at-dec)
open import DecidableTelescope using (dependent-context-dec)
open import BoolDecidable using (bool-dec)
open import DependentContextFixtures using (Code; code-dec)
open import DependentDiagramFixtures
open import DiagramBundle

------------------------------------------------------------------------
-- GENERATED, once per telescope: the packed context, its decision
-- procedure, the curried point, the two eliminators.

Ctx : Set
Ctx = CrispΣ Bool (λ b → CrispΣ (Code b) (λ _ → CrispUnitAt lzero))

ctx-dec : DecEq Ctx
ctx-dec = dependent-context-dec bool-dec
  (λ b → context-dec (code-dec b) unit-at-dec)

point : (@♭ b : Bool) (@♭ v : Code b) → Ctx
point b v = pair b (pair v end-at)

elim : ∀ {c} (P : Ctx → Set c)
     → ((@♭ b : Bool) (@♭ v : Code b) → P (point b v))
     → (g : Ctx) → P g
elim P leaf = unpack-dependent P (λ b t →
  unpack-crisp (λ t′ → P (pair b t′)) (λ v u →
  unpack-end-crisp (λ u′ → P (pair b (pair v u′))) (leaf b v) u) t)

elim♭ : ∀ {c} (P : (@♭ g : Ctx) → Set c)
      → ((@♭ b : Bool) (@♭ v : Code b) → P (point b v))
      → (@♭ g : Ctx) → P g
elim♭ P leaf = unpack-crisp P (λ b t →
  unpack-crisp (λ t′ → P (pair b t′)) (λ v u →
  unpack-end-crisp (λ u′ → P (pair b (pair v u′))) (leaf b v) u) t)

-- GENERATED, per diagram: the packed data, each an eliminator on a motive
-- and the user's datum as a curried leaf.

B̃ : Ctx → Set
B̃ = elim (λ _ → Set) (λ b v → BaseB b v)

C̃ : Ctx → Set
C̃ = elim (λ _ → Set) (λ b v → BaseC b v)

f̃ : (g : Ctx) → C̃ g → B̃ g
f̃ = elim (λ g → C̃ g → B̃ g) (λ b v → baseMap b v)

Ã : Σ Ctx B̃ → Set
Ã w = elim (λ g → B̃ g → Set) (λ b v → Fam b v) (fst w) (snd w)

dB̃ : (@♭ g : Ctx) → Discrete (B̃ g)
dB̃ = elim♭ (λ g → Discrete (B̃ g)) (λ b v → baseB-discrete b v)

B̃-set : (g : Ctx) → IsSet (B̃ g)
B̃-set = elim (λ g → IsSet (B̃ g)) (λ b v → baseB-set b v)

dC̃ : (@♭ g : Ctx) → Discrete (C̃ g)
dC̃ = elim♭ (λ g → Discrete (C̃ g)) (λ b v → baseC-discrete b v)

C̃-set : (g : Ctx) → IsSet (C̃ g)
C̃-set = elim (λ g → IsSet (C̃ g)) (λ b v → baseC-set b v)

------------------------------------------------------------------------
-- The user's open context. Capture happens here, before function
-- extensionality is in scope.

module Local (@♭ b : Bool) (@♭ v : Code b) where

  -- GENERATED: the two captures, of the local total sources in their
  -- native spelling.
  captured-B : CapturedShape (Σ (BaseB b v) (Fam b v))
  captured-B = shape

  captured-C : CapturedShape (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  captured-C = shape

  -- GENERATED: the presentations of the two stored families.
  private
    F-B : Ctx → Set
    F-B = C.Output.family captured-B

    F-C : Ctx → Set
    F-C = C.Output.family captured-C

    T-B : Ctx → Set
    T-B = LocalTotal B̃ Ã

    T-C : Ctx → Set
    T-C = LocalTotal C̃ (Reindexed f̃ Ã)

    out-B : (g : Ctx) → F-B g → T-B g
    out-B = elim (λ g → F-B g → T-B g) (λ b′ v′ → lower)

    in-B : (g : Ctx) → T-B g → F-B g
    in-B = elim (λ g → T-B g → F-B g) (λ b′ v′ → raise)

    sec-B : (g : Ctx) (z : T-B g) → out-B g (in-B g z) ≡ z
    sec-B = elim (λ g → (z : T-B g) → out-B g (in-B g z) ≡ z) (λ b′ v′ z → refl)

    ret-B : (g : Ctx) (u : F-B g) → in-B g (out-B g u) ≡ u
    ret-B = elim (λ g → (u : F-B g) → in-B g (out-B g u) ≡ u) (λ b′ v′ → raise-lower)

    out-C : (g : Ctx) → F-C g → T-C g
    out-C = elim (λ g → F-C g → T-C g) (λ b′ v′ → lower)

    in-C : (g : Ctx) → T-C g → F-C g
    in-C = elim (λ g → T-C g → F-C g) (λ b′ v′ → raise)

    sec-C : (g : Ctx) (z : T-C g) → out-C g (in-C g z) ≡ z
    sec-C = elim (λ g → (z : T-C g) → out-C g (in-C g z) ≡ z) (λ b′ v′ z → refl)

    ret-C : (g : Ctx) (u : F-C g) → in-C g (out-C g u) ≡ u
    ret-C = elim (λ g → (u : F-C g) → in-C g (out-C g u) ≡ u) (λ b′ v′ → raise-lower)

  -- GENERATED: the one value.
  diagram : CapturedDiagram lzero
  diagram = captured-diagram Ctx telescope-discrete ctx-dec B̃ C̃
    dB̃ B̃-set dC̃ C̃-set f̃ Ã (point b v)
    F-B F-C (C.Output.whole-context captured-B) (C.Output.whole-context captured-C)
    out-B in-B sec-B ret-B out-C in-C sec-C ret-C

  ----------------------------------------------------------------------
  -- Checks that need no function extensionality.

  -- The packed data at the stored point are the native expressions.
  base-B : CapturedField.B diagram (CapturedField.point diagram) ≡ BaseB b v
  base-B = refl

  map-here : CapturedField.f diagram (CapturedField.point diagram) ≡ baseMap b v
  map-here = refl

  source-B : CapturedField.TB diagram (CapturedField.point diagram)
           ≡ Σ (BaseB b v) (Fam b v)
  source-B = refl

  source-C : CapturedField.TC diagram (CapturedField.point diagram)
           ≡ Σ (BaseC b v) (λ k → Fam b v (baseMap b v k))
  source-C = refl

  -- The wrappers rebuilt from the bundle ARE the two captures.
  local-is-captured-B : CapturedField.localB diagram ≡ captured-B
  local-is-captured-B = refl

  local-is-captured-C : CapturedField.localC diagram ≡ captured-C
  local-is-captured-C = refl

  ----------------------------------------------------------------------
  -- USER: the library applied to the one generated name, after function
  -- extensionality. No point, no At.

  module WithFE (@♭ fe : FunExtAt lzero) where

    module D = AssembleCaptured fe diagram

    -- The canonical comparison of the local diagram, for the reflections
    -- of the two captures made above, natively typed, and its unit law.
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

    -- Kernel is the total-form statement about the public module Whole.
    kernel-is : D.Kernel ≡ D.Whole.TotalComparisonIsEquivalence
    kernel-is = refl

    -- The raw reflections of the two captures have the captures' own
    -- total carriers and units, by definition; the default ones are their
    -- sealed copies.
    raw-carrier : Output.Total D.CaptureB.raw-reflection ≡ C.Output.carrier captured-B
    raw-carrier = refl

    raw-unit : Output.unit D.CaptureB.raw-reflection ≡ C.Output.unit captured-B
    raw-unit = refl

    default-is-raw : D.reflB ≡ D.CaptureB.raw-reflection
    default-is-raw = D.CaptureB.reflection-path

    -- The restricted reflections of the whole diagram at the stored
    -- point, in the library's own terms (not restated natively:
    -- fable-impl-11, RESULTS-FABLE.txt section I).
    raw-result : D.Kernel → D.Here.Raw.ComparisonIsEquivalence
    raw-result = D.Here.raw-from-kernel

    -- THE BOUNDARY OF THE OPAQUE COPIES. The library derives everything
    -- from opaque copies of the two whole shape data. A proof of the
    -- kernel statement will be about reflections of the whole diagram
    -- obtained in some other way. Here: the relative reflections derived
    -- directly from D.derivedB and D.derivedC, which are transparent and
    -- have the total carriers and units of the two captures' payloads.
    -- KernelFrom carries ORDINARY evidence about their comparison to
    -- Kernel, and from-kernel to the local conclusion. One canonical
    -- transfer; no transport along wholeB-path.
    originalB : RelativeShapeOver (Σ Ctx B̃) D.wholeB-discrete Ã
    originalB = Converse.relative fe {dΓ = D.wholeB-discrete} D.wholeB-set
      D.derivedB

    originalC : RelativeShapeOver (Σ Ctx C̃) D.wholeC-discrete (Reindexed f̃ Ã)
    originalC = Converse.relative fe {dΓ = D.wholeC-discrete} D.wholeC-set
      D.derivedC

    module Original = D.KernelFrom originalB originalC

    kernel-from-original : Original.Supplied.TotalComparisonIsEquivalence
                         → D.Kernel
    kernel-from-original = Original.kernel

    local-from-original : Original.Supplied.TotalComparisonIsEquivalence
                        → (k : BaseC b v) → IsEquiv (comparison k)
    local-from-original e = result (Original.kernel e)

    -- The total carrier of the transparent whole reflection is the total
    -- carrier of the capture's payload: the whole data are derived from
    -- the two contextual choices and from nothing else.
    whole-carrier : Output.Total originalB
                  ≡ Output.Total (C.Output.whole-context captured-B)
    whole-carrier = refl

