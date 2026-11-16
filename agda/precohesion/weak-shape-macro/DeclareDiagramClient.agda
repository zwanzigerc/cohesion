{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A closed client with NOTHING typed in for the generator. Claude (Fable),
-- 13 November 2026; generator checkpoint after fable-impl-11. Compare
-- AssemblyClientA of fable-impl-11, whose parts marked GENERATED (two
-- captures and the bundle value, per diagram) were written by hand. Here
-- each diagram is one declaration; everything after it is the user's
-- side, and it is the user's side of AssemblyClientA.
--
-- Also here: level one (the fibres are the universe Set, no sethood of it
-- is assumed), and the rebuilt wrapper at both levels.
--
-- Declarations of this file: four diagrams, five shape axioms
-- (DiagramInventory, at the end; the family of the level-one diagram is
-- constant, so its two sources coincide and it has one axiom). The
-- fixtures' postulates are imported.
module DeclareDiagramClient where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)
open import CaptureContext using (raise)
open import ShapeElim using (raise-set; raise-discrete)
open import DependentDiagramFixtures
  using (Row; Col; row-discrete; row-set; col-discrete; col-set; step; Cell)
open import AssemblyFixtures
  using (collapse; Colours; ℓ₁; Bool₁; bool₁-discrete; bool₁-set; bool₁-dec;
         collapse₁; Types)
open import DiagramBundle
open import DiagramData using (closed-seed; module ClosedSeed)
open import DeclareDiagram using (declareClosedDiagram)
open import DiagramInventory using (shape-axioms)

------------------------------------------------------------------------
-- Diagram 1: step : Col → Row with the family Cell. No decision
-- procedure is supplied for Row or Col; Cell has arbitrary fibres. The
-- conclusion is conditional on Kernel, an ordinary hypothesis.

unquoteDecl cells =
  declareClosedDiagram cells row-discrete row-set col-discrete col-set step Cell

module Cells (@♭ fe : FunExtAt lzero) where

  module D = AssembleClosed fe cells

  comparison : (k : Col)
             → Output.family D.reflC k → Output.family D.reflB (step k)
  comparison = D.Diagram.comparison

  unit-law : (k : Col) (a : Cell (step k))
           → comparison k (Output.family-unit D.reflC k a)
             ≡ Output.family-unit D.reflB (step k) a
  unit-law = D.Diagram.comparison-on-unit

  result : D.Kernel → (k : Col) → IsEquiv (comparison k)
  result = D.from-kernel

  kernel-is : D.Kernel ≡ D.Whole.TotalComparisonIsEquivalence
  kernel-is = refl

  raw-result : D.Kernel → D.Whole.ComparisonIsEquivalence
  raw-result = D.raw-from-kernel

  -- The library's opaque copies are copies of the generated payloads.
  payload-path : D.payloadB ≡ ClosedField.KB cells
  payload-path = D.payloadB-path

------------------------------------------------------------------------
-- Diagram 2: both bases decidable, the conclusion without hypothesis.

unquoteDecl colours =
  declareClosedDiagram colours
    bool-is-discrete bool-is-set bool-is-discrete bool-is-set collapse Colours

module Colouring (@♭ fe : FunExtAt lzero) where

  module D = AssembleClosed fe colours

  comparison : (c : Bool)
             → Output.family D.reflC c → Output.family D.reflB (collapse c)
  comparison = D.Diagram.comparison

  unconditional : (c : Bool) → IsEquiv (comparison c)
  unconditional = D.decidable bool-dec bool-dec

------------------------------------------------------------------------
-- Diagram 3: level one. The bundle is in Set₂, the kernel in Set₁. Types
-- is the constant family at Set, so  Σ Bool₁ (Types ∘ collapse₁)  is
-- Σ Bool₁ Types  by conversion: one axiom, and the map collapse₁ is still
-- the map of the bundle.

unquoteDecl types =
  declareClosedDiagram types
    bool₁-discrete bool₁-set bool₁-discrete bool₁-set collapse₁ Types

bundle-at-one : ClosedDiagram ℓ₁
bundle-at-one = types

module One (@♭ fe : FunExtAt ℓ₁) where

  module D = AssembleClosed fe types

  kernel-at-one : Set₁
  kernel-at-one = D.Kernel

  comparison : (x : Bool₁)
             → Output.family D.reflC x → Output.family D.reflB (collapse₁ x)
  comparison = D.Diagram.comparison

  unit-law : (x : Bool₁) (T : Set)
           → comparison x (Output.family-unit D.reflC x T)
             ≡ Output.family-unit D.reflB (collapse₁ x) T
  unit-law = D.Diagram.comparison-on-unit

  unconditional : (x : Bool₁) → IsEquiv (comparison x)
  unconditional = D.decidable bool₁-dec bool₁-dec

types-one-choice : ClosedField.KB types ≡ ClosedField.KC types
types-one-choice = refl

types-map : ClosedField.f types ≡ collapse₁
types-map = refl

-- The same diagram with every argument written INLINE: applications with
-- hidden arguments, a constructor, lambdas. Quotation drops parameters
-- from such terms; elaboration against the argument types of the bundle
-- constructor restores them, and the native final check compares the
-- result with the typed arguments. The bundle is the one above.
unquoteDecl types-inline =
  declareClosedDiagram types-inline
    (raise-discrete bool-is-discrete) (raise-set bool-is-set)
    (raise-discrete bool-is-discrete) (raise-set bool-is-set)
    (λ _ → raise false) (λ _ → Set)

inline-same : types-inline ≡ types
inline-same = refl

-- An ordinary request at level one reuses the bundle's choice; the
-- wrapper type is the one a capture infers, CapturedShape {ℓ₁} {ℓ₁}.
types-again : CapturedShape (Σ Bool₁ Types)
types-again = shape

types-again-same : types-again ≡ ClosedSeed.seedB types
types-again-same = refl

------------------------------------------------------------------------
-- The wrapper of a capture in the empty context is rebuilt from its whole
-- payload by the constructor alone, at level zero and at level one. This
-- is a statement about such wrappers; a wrapper in general has another
-- context and another point.

first : CapturedShape (Σ Bool Colours)
first = shape

rebuilt : CapturedShape (Σ Bool Colours)
rebuilt = closed-seed (Σ Bool Colours) (C.Output.whole-context first)

rebuilt-same : rebuilt ≡ first
rebuilt-same = refl

first₁ : CapturedShape (Σ Bool₁ (Types ∘ collapse₁))
first₁ = shape

rebuilt₁ : CapturedShape {ℓ = ℓ₁} (Σ Bool₁ (Types ∘ collapse₁))
rebuilt₁ = closed-seed (Σ Bool₁ (Types ∘ collapse₁)) (C.Output.whole-context first₁)

rebuilt₁-same : rebuilt₁ ≡ first₁
rebuilt₁-same = refl

------------------------------------------------------------------------
-- Rooted inventory: two diagrams with two distinct sources each, one
-- with coinciding sources and its inline repetition; the three ordinary
-- requests listed are hits on the bundles of this file.

all-axioms : Nat
all-axioms = shape-axioms
  (quote cells ∷ quote colours ∷ quote types ∷ quote types-inline ∷ [])
  (quote types-again ∷ quote first ∷ quote first₁ ∷ [])

all-axioms-are : all-axioms ≡ 5
all-axioms-are = refl
