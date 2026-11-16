{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Further cases of the direct generator (DeclareCapturedDiagram). Claude
-- (Fable), 13 November 2026; step S3b. The dependent Bool/Code client is
-- AssemblyClientGenerated; here:
--
--   1. Named     the same diagram given as NAMES of definitions of the
--                module, and the decision procedures as a named list;
--                next to it the inline form; the two bundles have the same
--                closed fields
--   2. One       a telescope of length one at LEVEL one; one shape for the
--                two sources
--   3. Three     a telescope of length three; an inline family that uses
--                the newest variable
--   4. Maps      a CONSTANT family and two different maps: the two bundles
--                keep their maps apart
--   5. Procedures  a decision procedure given through a definition of the
--                module that is handed the newest variable and ignores it:
--                the preparation unfolds it, and what remains is over the
--                prefix
--   6. Recovered  inputs whose syntax drops parameters: a projection given
--                as a function, and pairs inside the family
--   7. Hidden    why the map is audited on its own: with a constant
--                family, a capture of the C-side source is ACCEPTED when
--                the map is a postulate of the module, because the source
--                does not show the map. The generator refuses that map
--                (CapturedDiagramOpaqueMap).
--
-- REUSE. A bundle made by the generator is registered (step S3c): a later
-- request for one of its two sources in the same context takes the
-- bundle's capture. So the second bundle of Named and of Maps declares
-- nothing, and the counts below are 2 and 1. The cases of reuse proper
-- are in DeclareCapturedDiagramReuse.
module DeclareCapturedDiagramExamples where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureContext using (CrispΣ; pair; CrispUnitAt; end-at)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)
open import DecidableBase using (DecEq)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalChoice using (×-set)
open import DependentContextFixtures using (Code; code-dec)
open import DependentDiagramFixtures
open import AssemblyFixtures
open import DiagramBundle
open import DeclareCapturedDiagram
open import DiagramInventory using (shape-axioms)

private
  module F = CapturedField

------------------------------------------------------------------------
-- 1. Named definitions of the module, and inline expressions.

module Named (@♭ b : Bool) (@♭ v : Code b) where

  -- USER: the diagram as definitions of this module.
  Base : Set
  Base = BaseB b v

  Index : Set
  Index = BaseC b v

  along : Index → Base
  along = baseMap b v

  Fibre : Base → Set
  Fibre = Fam b v

  base-discrete : Discrete Base
  base-discrete = baseB-discrete b v

  base-set : IsSet Base
  base-set = baseB-set b v

  index-discrete : Discrete Index
  index-discrete = baseC-discrete b v

  index-set : IsSet Index
  index-set = baseC-set b v

  procedures : Deciders
  procedures = bool-dec ∷ code-dec b ∷ []

  unquoteDecl named =
    declareCapturedDiagram named procedures
      base-discrete base-set index-discrete index-set along Fibre

  -- The same diagram, inline.
  unquoteDecl inline =
    declareCapturedDiagram inline (bool-dec ∷ code-dec b ∷ [])
      (baseB-discrete b v) (baseB-set b v)
      (baseC-discrete b v) (baseC-set b v)
      (baseMap b v) (Fam b v)

  -- At the stored point the named bundle has the definitions.
  named-map : F.f named (F.point named) ≡ along
  named-map = refl

  named-family : FibreAt (F.A named) (F.point named) ≡ Fibre
  named-family = refl

  named-evidence : F.dC named (F.point named) ≡ index-discrete
  named-evidence = refl

  -- The CLOSED fields of the two bundles are the same: packed context,
  -- bases, map, family, and the stored families and presentation maps.
  same-context : F.G named ≡ F.G inline
  same-context = refl

  same-base : F.B named ≡ F.B inline
  same-base = refl

  same-map : F.f named ≡ F.f inline
  same-map = refl

  same-family : F.A named ≡ F.A inline
  same-family = refl

  same-stored : F.FC named ≡ F.FC inline
  same-stored = refl

  same-out : F.outC named ≡ F.outC inline
  same-out = refl

  -- So are the payloads: the second call found the captures of the first
  -- (DeclareCapturedDiagramReuse has the equalities). Two shapes in all.
  namedB : CapturedShape (Σ Base Fibre)
  namedB = F.localB named

  namedC : CapturedShape (Σ Index (λ k → Fibre (along k)))
  namedC = F.localC named

  inlineB : CapturedShape (Σ (BaseB b v) (Fam b v))
  inlineB = F.localB inline

  inlineC : CapturedShape (Σ (BaseC b v) (λ k → Fam b v (baseMap b v k)))
  inlineC = F.localC inline

  two-shapes : shape-axioms []
                 (quote namedB ∷ quote namedC ∷ quote inlineB ∷ quote inlineC ∷ [])
             ≡ 2
  two-shapes = refl

------------------------------------------------------------------------
-- 2. Length one, level one. The base is Bool raised to Set₁, the fibres
-- are the universe Set, the map depends on the variable of the context.

module One (@♭ b : Bool) where

  unquoteDecl cells₁ =
    declareCapturedDiagram cells₁ (bool-dec ∷ [])
      bool₁-discrete bool₁-set bool₁-discrete bool₁-set (pick b) Types

  bundle-at-one : CapturedDiagram ℓ₁
  bundle-at-one = cells₁

  context-at-one : F.G cells₁ ≡ CrispΣ Bool (λ _ → CrispUnitAt ℓ₁)
  context-at-one = refl

  map-at-one : F.f cells₁ (F.point cells₁) ≡ pick b
  map-at-one = refl

  family-at-one : FibreAt (F.A cells₁) (F.point cells₁) ≡ Types
  family-at-one = refl

  -- The two sources are one type, and the second capture took the first:
  -- one shape.
  oneB : CapturedShape (Σ Bool₁ Types)
  oneB = F.localB cells₁

  oneC : CapturedShape (Σ Bool₁ (λ x → Types (pick b x)))
  oneC = F.localC cells₁

  one-shape : shape-axioms [] (quote oneB ∷ quote oneC ∷ []) ≡ 1
  one-shape = refl

  module WithFE (@♭ fe : FunExtAt ℓ₁) where

    module D = AssembleCaptured fe cells₁

    comparison : (x : Bool₁)
               → Output.family D.reflC x → Output.family D.reflB (pick b x)
    comparison = D.Diagram.comparison

    -- The unit of the reflection at a type of Set.
    unit-law : (x : Bool₁) (T : Set)
             → comparison x (Output.family-unit D.reflC x T)
               ≡ Output.family-unit D.reflB (pick b x) T
    unit-law = D.Diagram.comparison-on-unit

    conditional : D.Kernel → (x : Bool₁) → IsEquiv (comparison x)
    conditional = D.from-kernel

    -- The base has decidable equality: no hypothesis.
    unconditional : (x : Bool₁) → IsEquiv (comparison x)
    unconditional = D.decidable bool₁-dec bool₁-dec

------------------------------------------------------------------------
-- 3. Length three. The family is written inline and uses the newest
-- variable; the procedure for the second variable mentions the first.

module Three (@♭ b : Bool) (@♭ v : Code b) (@♭ w : Bool) where

  unquoteDecl cells₃ =
    declareCapturedDiagram cells₃ (bool-dec ∷ code-dec b ∷ bool-dec ∷ [])
      (baseB-discrete b v) (baseB-set b v)
      (baseC-discrete b v) (baseC-set b v)
      (baseMap b v) (λ r → Fam b v r × Colours w)

  context-of-three : F.G cells₃
                   ≡ CrispΣ Bool (λ b′ → CrispΣ (Code b′) (λ _ →
                       CrispΣ Bool (λ _ → CrispUnitAt lzero)))
  context-of-three = refl

  point-of-three : F.point cells₃ ≡ pair b (pair v (pair w end-at))
  point-of-three = refl

  map-of-three : F.f cells₃ (F.point cells₃) ≡ baseMap b v
  map-of-three = refl

  family-of-three : FibreAt (F.A cells₃) (F.point cells₃)
                  ≡ (λ r → Fam b v r × Colours w)
  family-of-three = refl

  source-of-three : F.TC cells₃ (F.point cells₃)
                  ≡ Σ (BaseC b v) (λ k → Fam b v (baseMap b v k) × Colours w)
  source-of-three = refl

  module WithFE (@♭ fe : FunExtAt lzero) where

    module D = AssembleCaptured fe cells₃

    comparison : (k : BaseC b v)
               → Output.family D.reflC k → Output.family D.reflB (baseMap b v k)
    comparison = D.Diagram.comparison

    result : D.Kernel → (k : BaseC b v) → IsEquiv (comparison k)
    result = D.from-kernel

------------------------------------------------------------------------
-- 4. A constant family and two maps. The reindexed family is the same
-- constant family for every map, so neither source shows the map. Each
-- bundle has its own.

module Maps (@♭ b : Bool) where

  unquoteDecl kept =
    declareCapturedDiagram kept (bool-dec ∷ [])
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set keep Constant

  unquoteDecl collapsed =
    declareCapturedDiagram collapsed (bool-dec ∷ [])
      bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Constant

  kept-map : F.f kept (F.point kept) ≡ keep
  kept-map = refl

  collapsed-map : F.f collapsed (F.point collapsed) ≡ collapse
  collapsed-map = refl

  -- The sources of the two bundles are one type, on both sides.
  one-source : F.TC kept (F.point kept) ≡ F.TB collapsed (F.point collapsed)
  one-source = refl

  -- The packed maps differ already at the stored point.
  maps-differ : F.f kept (F.point kept) true ≡ true
  maps-differ = refl

  maps-differ′ : F.f collapsed (F.point collapsed) true ≡ false
  maps-differ′ = refl

  keptB : CapturedShape (Σ Bool Constant)
  keptB = F.localB kept

  keptC : CapturedShape (Σ Bool (λ x → Constant (keep x)))
  keptC = F.localC kept

  collapsedB : CapturedShape (Σ Bool Constant)
  collapsedB = F.localB collapsed

  collapsedC : CapturedShape (Σ Bool (λ x → Constant (collapse x)))
  collapsedC = F.localC collapsed

  -- One shape for the first bundle (the second capture of a call takes
  -- the first), and the second bundle takes it too: one in all. The two
  -- bundles remain different: their maps are.
  kept-shape : shape-axioms [] (quote keptB ∷ quote keptC ∷ []) ≡ 1
  kept-shape = refl

  one-shape : shape-axioms []
                (quote keptB ∷ quote keptC ∷ quote collapsedB ∷ quote collapsedC ∷ [])
            ≡ 1
  one-shape = refl

  -- The check that the generator has Agda make, stated by hand for the
  -- bundle with the map keep: accepted.
  kept-certificate : CapturedDiagramOf
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set keep Constant
    keptB keptC kept
  kept-certificate = bundled kept

------------------------------------------------------------------------
-- 5. A decision procedure through a definition of the module. The term
-- at-point v mentions v. The preparation exposes definitions of the file
-- of the call in the native context; what it leaves is code-dec b, which
-- is over b alone. The same body behind an IMPORTED name is not unfolded
-- and is refused (CapturedDiagramProcedureLater).

module Procedures (@♭ b : Bool) (@♭ v : Code b) where

  at-point : Code b → DecEq (Code b)
  at-point _ = code-dec b

  unquoteDecl cells =
    declareCapturedDiagram cells (bool-dec ∷ at-point v ∷ [])
      (baseB-discrete b v) (baseB-set b v)
      (baseC-discrete b v) (baseC-set b v)
      (baseMap b v) (Fam b v)

  -- The packed procedure does not depend on how it was given.
  same-procedure : F.dec cells ≡ F.dec (Named.inline b v)
  same-procedure = refl

------------------------------------------------------------------------
-- 6. Parameters that reflected syntax drops. The map is a projection
-- given as a function; the family is a type of paths between pairs and
-- mentions the variable of the context. Quoted, the projection and the
-- pair constructors have lost their parameters; the preparation writes
-- them out again (CaptureExplicit), and the audited terms are complete.

module Recovered (@♭ b : Bool) where

  unquoteDecl cells =
    declareCapturedDiagram cells (bool-dec ∷ [])
      bool-is-discrete bool-is-set
      (SigmaDiscrete.discrete bool-is-discrete (λ _ → bool-is-discrete))
      (×-set bool-is-set bool-is-set)
      fst (λ x → (x , b) ≡ (true , false))

  recovered-map : F.f cells (F.point cells) ≡ fst
  recovered-map = refl

  recovered-family : FibreAt (F.A cells) (F.point cells)
                   ≡ (λ x → (x , b) ≡ (true , false))
  recovered-family = refl

  recovered-source : F.TC cells (F.point cells)
                   ≡ Σ (Bool × Bool) (λ k → (fst k , b) ≡ (true , false))
  recovered-source = refl

------------------------------------------------------------------------
-- 7. A map that a source does not show. `hidden` is a postulate of this
-- module: a test input that conceals the variable of the context, and an
-- assumption of this file. The family is constant, so the C-side source
-- of the diagram (Bool, Bool, hidden, Constant) is Σ Bool (λ _ → Bool)
-- once the definition of Constant is exposed, and a capture of it is
-- ACCEPTED: nothing of the map is left to audit. Reading the map off the
-- sources would therefore let it through. The generator prepares the map
-- as a term of its own and refuses it (CapturedDiagramOpaqueMap).

module Hidden (@♭ b : Bool) where

  postulate
    hidden : Bool → Bool

  source-C : CapturedShape (Σ Bool (λ x → Constant (hidden x)))
  source-C = shape
