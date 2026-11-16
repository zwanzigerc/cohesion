{-# OPTIONS --cohesion --without-K --flat-split #-}

-- One value for a whole diagram: the bundles that an automatic-assembly
-- frontend is to produce, their accessors, and the library applied to a
-- bundle. Claude (Fable), 13 November 2026; fable-impl-11. Step S1 of
-- AUTOMATIC-ASSEMBLY-PLAN-FABLE-01 (layer L2). Postulate-free; no
-- reflection; no capture.
--
--   ClosedDiagram ℓ   a closed diagram with the closed payloads of its two
--                     total sources
--   OpenDiagram ℓ     a diagram over a decidable context, with the closed
--                     payloads of its two WHOLE total sources
--   ClosedField, OpenField   the accessors
--   AssembleClosed fe d      DiagramAssembly.Closed for the fields of d
--   AssembleOpen fe d        DiagramAssembly.Open for the fields of d
--
-- A bundle PACKAGES HYPOTHESES. Its constructor takes both closed payloads
-- as arguments: no value of a bundle type can be made without already
-- having them. It is not a provider of shapes and it promotes no captured
-- fibre to a terminal reflection.
--
-- LEVELS. Both bundle types are parameterised by a crisp level ℓ, the
-- common level of the diagram, and live in Set (lsuc ℓ): they store types
-- of Set ℓ and payloads of Set (lsuc ℓ). That is the least universe that
-- holds them: the same declaration in Set ℓ is refused (the negative
-- test BundleTooSmall.agda.fail of this directory). The plan probe had
-- them one level higher than necessary.
--
-- FORM OF THE CONSTRUCTORS. Every argument is crisp, as for CapturedShape,
-- and every accessor takes the bundle crisply. Three argument types are
-- written through the abbreviations AllSets, MapsOver and Reindexed: in a
-- constructor telescope, a type written inline as a function type with an
-- ORDINARY binder that is applied to earlier crisp arguments is refused
-- (plan probe AssemblyInlinePi.agda.fail). The abbreviations take the
-- crisp data crisply and change no quantifier:
--   dB, dC          take a CRISP point of the context
--   B-set, C-set, f take an ORDINARY point of the context
--   A               takes an ORDINARY point of Σ G B
module DiagramBundle where

open import Foundations
open import RelativeSliceShape
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion using (Closed; ShapeData)
open import DecidableBase using (DecEq; decidable-set)
open import CapturedShape using (CapturedShape; captured)
open import TotalBridge using (module TotalData)
open import GlobalChoice using (module Along)
open import DecidableReindexing using (module Stable)
import DiagramAssembly

-- The abbreviations AllSets, MapsOver, Reindexed, LocalTotal, SectionOver,
-- DiscreteOver, FibreAt, OverTotal, the presentations (Presentation,
-- lowering, Presented), the captured bundle (CapturedDiagram,
-- CapturedField) and the two certificate types of the direct generator
-- (PackedDiagramOf, CapturedDiagramOf) are declared in DiagramData since
-- step S3c: the shared lookup of the capture frontend consults visible
-- captured bundles and must not import the assembly library. They are
-- re-exported here unchanged, under the same names.
open import DiagramData public
  using (AllSets; MapsOver; Reindexed; LocalTotal; SectionOver;
         DiscreteOver; FibreAt; OverTotal;
         Presentation; lowering; module Presented;
         CapturedDiagram; captured-diagram; module CapturedField;
         PackedDiagramOf; packed; CapturedDiagramOf; bundled)

------------------------------------------------------------------------
-- Closed diagrams.

-- The declarations ClosedDiagram and ClosedField are in DiagramData since
-- the generator checkpoint after fable-impl-11 (the capture frontend
-- consults visible bundles and must not import the assembly library).
-- They are re-exported here unchanged.
open import DiagramData public
  using (ClosedDiagram; closed-diagram; module ClosedField)

module AssembleClosed
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ d : ClosedDiagram ℓ) where

  open DiagramAssembly.Closed fe
    (ClosedField.dB d) (ClosedField.B-set d)
    (ClosedField.dC d) (ClosedField.C-set d)
    (ClosedField.f d) (ClosedField.A d)
    (ClosedField.KB d) (ClosedField.KC d) public

------------------------------------------------------------------------
-- Diagrams over a decidable context.

data OpenDiagram (@♭ ℓ : Level) : Set (lsuc ℓ) where
  open-diagram :
    (@♭ G : Set ℓ) (@♭ dG : Discrete G) (@♭ dec : DecEq G)
    (@♭ B C : G → Set ℓ)
    (@♭ dB : (@♭ g : G) → Discrete (B g)) (@♭ B-set : AllSets B)
    (@♭ dC : (@♭ g : G) → Discrete (C g)) (@♭ C-set : AllSets C)
    (@♭ f : MapsOver C B)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ KB : Closed (Σ (Σ G B) A))
    (@♭ KC : Closed (Σ (Σ G C) (Reindexed f A)))
    → OpenDiagram ℓ

module OpenField {@♭ ℓ : Level} where

  G : (@♭ d : OpenDiagram ℓ) → Set ℓ
  G (open-diagram G _ _ _ _ _ _ _ _ _ _ _ _) = G

  dG : (@♭ d : OpenDiagram ℓ) → Discrete (G d)
  dG (open-diagram _ dG _ _ _ _ _ _ _ _ _ _ _) = dG

  dec : (@♭ d : OpenDiagram ℓ) → DecEq (G d)
  dec (open-diagram _ _ dec _ _ _ _ _ _ _ _ _ _) = dec

  B : (@♭ d : OpenDiagram ℓ) → G d → Set ℓ
  B (open-diagram _ _ _ B _ _ _ _ _ _ _ _ _) = B

  C : (@♭ d : OpenDiagram ℓ) → G d → Set ℓ
  C (open-diagram _ _ _ _ C _ _ _ _ _ _ _ _) = C

  dB : (@♭ d : OpenDiagram ℓ) (@♭ g : G d) → Discrete (B d g)
  dB (open-diagram _ _ _ _ _ dB _ _ _ _ _ _ _) = dB

  B-set : (@♭ d : OpenDiagram ℓ) (g : G d) → IsSet (B d g)
  B-set (open-diagram _ _ _ _ _ _ B-set _ _ _ _ _ _) = B-set

  dC : (@♭ d : OpenDiagram ℓ) (@♭ g : G d) → Discrete (C d g)
  dC (open-diagram _ _ _ _ _ _ _ dC _ _ _ _ _) = dC

  C-set : (@♭ d : OpenDiagram ℓ) (g : G d) → IsSet (C d g)
  C-set (open-diagram _ _ _ _ _ _ _ _ C-set _ _ _ _) = C-set

  f : (@♭ d : OpenDiagram ℓ) (g : G d) → C d g → B d g
  f (open-diagram _ _ _ _ _ _ _ _ _ f _ _ _) = f

  A : (@♭ d : OpenDiagram ℓ) → Σ (G d) (B d) → Set ℓ
  A (open-diagram _ _ _ _ _ _ _ _ _ _ A _ _) = A

  KB : (@♭ d : OpenDiagram ℓ) → Closed (Σ (Σ (G d) (B d)) (A d))
  KB (open-diagram _ _ _ _ _ _ _ _ _ _ _ KB _) = KB

  KC : (@♭ d : OpenDiagram ℓ)
     → Closed (Σ (Σ (G d) (C d)) (Reindexed (f d) (A d)))
  KC (open-diagram _ _ _ _ _ _ _ _ _ _ _ _ KC) = KC

module AssembleOpen
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ d : OpenDiagram ℓ) where

  open DiagramAssembly.Open fe {dG = OpenField.dG d} (OpenField.dec d)
    (OpenField.dB d) (OpenField.B-set d) (OpenField.dC d) (OpenField.C-set d)
    (OpenField.f d) (OpenField.A d) (OpenField.KB d) (OpenField.KC d) public

------------------------------------------------------------------------
-- Captured diagrams: a diagram stated INSIDE a context, with the two
-- captures made there (step S3a; the direct generator of step S3b makes
-- one). The declarations CapturedDiagram and CapturedField, with their
-- description, and the two certificate types are in DiagramData (see the
-- note at the head of this module). What follows is the library applied
-- to a captured bundle.

-- The library applied to a captured bundle.
--
--   derivedB, derivedC   terminal shape data of the two WHOLE total
--                        sources: the total spaces of the two contextual
--                        payloads (TotalBridge.TotalData; sethood of G
--                        from its decision procedure), moved along the
--                        source isomorphisms that the pointwise
--                        presentations give (GlobalChoice.Along). Their
--                        carriers are the TOTAL carriers of the payloads
--                        (not the selected fibre of a capture); their
--                        units are the payloads' units precomposed with
--                        the source presentation. TRANSPARENT: these are
--                        the original choices.
--   (the names of DiagramAssembly.OpenData at these data)
--                        Kernel, Whole, KernelFrom, At, … ; in particular
--                        Kernel is the statement about the WHOLE diagram
--                        and an ordinary hypothesis. It is stated for
--                        reflections derived from THESE two contextual
--                        choices; another choice of whole reflections,
--                        for instance a closed one, reaches it through
--                        KernelFrom.
--   Here                 At the stored point. No point is written by the
--                        user of a bundle.
--   CaptureB, CaptureC   DiagramAssembly.FromCapture at the two rebuilt
--                        wrappers: the raw reflections with the carriers
--                        and units of the captures, and the sealed ones.
--   reflB, reflC         the DEFAULT outputs: the sealed reflections of
--                        the two ORIGINAL captures at the stored point
--   Diagram              the canonical comparison of the local diagram for
--                        them, with its unit law
--   from-kernel          Kernel gives that it is an equivalence
--   total-from-kernel    the same in total form
--   decidable            the same conclusion with no hypothesis when both
--                        LOCAL bases at the stored point have decidable
--                        equality (DecidableReindexing)
--   Fresh                the instance of Here.ForPayloads behind these.
--                        The square of the comparison of the default
--                        outputs with the canonical bridges from Here's
--                        restricted reflections is Fresh.FromRaw.natural,
--                        under its own type. Here.Sealing.natural is a
--                        different square: it relates Here's restricted
--                        raw reflections to THEIR sealed copies.
-- Policy as in fable-impl-11: results about the default outputs can be
-- restated natively; results about raw outputs are used in the library's
-- own terms.

module AssembleCaptured
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ d : CapturedDiagram ℓ) where

  private
    module F = CapturedField

    toB : Σ (F.G d) (F.FB d) → Σ (Σ (F.G d) (F.B d)) (F.A d)
    toB w = (fst w , fst (F.outB d (fst w) (snd w))) , snd (F.outB d (fst w) (snd w))

    fromB : Σ (Σ (F.G d) (F.B d)) (F.A d) → Σ (F.G d) (F.FB d)
    fromB w = fst (fst w) , F.inB d (fst (fst w)) (snd (fst w) , snd w)

    toB-fromB : (w : Σ (Σ (F.G d) (F.B d)) (F.A d)) → toB (fromB w) ≡ w
    toB-fromB w = ap (λ z → (fst (fst w) , fst z) , snd z)
      (F.secB d (fst (fst w)) (snd (fst w) , snd w))

    fromB-toB : (w : Σ (F.G d) (F.FB d)) → fromB (toB w) ≡ w
    fromB-toB w = ap (λ u → fst w , u) (F.retB d (fst w) (snd w))

    toC : Σ (F.G d) (F.FC d)
        → Σ (Σ (F.G d) (F.C d)) (Reindexed (F.f d) (F.A d))
    toC w = (fst w , fst (F.outC d (fst w) (snd w))) , snd (F.outC d (fst w) (snd w))

    fromC : Σ (Σ (F.G d) (F.C d)) (Reindexed (F.f d) (F.A d))
          → Σ (F.G d) (F.FC d)
    fromC w = fst (fst w) , F.inC d (fst (fst w)) (snd (fst w) , snd w)

    toC-fromC : (w : Σ (Σ (F.G d) (F.C d)) (Reindexed (F.f d) (F.A d)))
              → toC (fromC w) ≡ w
    toC-fromC w = ap (λ z → (fst (fst w) , fst z) , snd z)
      (F.secC d (fst (fst w)) (snd (fst w) , snd w))

    fromC-toC : (w : Σ (F.G d) (F.FC d)) → fromC (toC w) ≡ w
    fromC-toC w = ap (λ u → fst w , u) (F.retC d (fst w) (snd w))

  derivedB : ShapeData (Σ (Σ (F.G d) (F.B d)) (F.A d))
  derivedB = Along.along toB fromB toB-fromB fromB-toB
    (TotalData.total-data fe {dΓ = F.dG d} (decidable-set (F.dec d)) (F.KB d))

  derivedC : ShapeData (Σ (Σ (F.G d) (F.C d)) (Reindexed (F.f d) (F.A d)))
  derivedC = Along.along toC fromC toC-fromC fromC-toC
    (TotalData.total-data fe {dΓ = F.dG d} (decidable-set (F.dec d)) (F.KC d))

  open DiagramAssembly.OpenData fe {dG = F.dG d} (F.dec d)
    (F.dB d) (F.B-set d) (F.dC d) (F.C-set d)
    (F.f d) (F.A d) derivedB derivedC public

  module Here = At (F.point d)

  module CaptureB = DiagramAssembly.FromCapture fe
    (F.dB d (F.point d)) (F.B-set d (F.point d)) (F.localB d) (F.dec d)

  module CaptureC = DiagramAssembly.FromCapture fe
    (F.dC d (F.point d)) (F.C-set d (F.point d)) (F.localC d) (F.dec d)

  module Fresh = Here.ForPayloads CaptureB.reflection CaptureC.reflection

  open CaptureB public using () renaming (reflection to reflB)
  open CaptureC public using () renaming (reflection to reflC)
  open Fresh public using () renaming (module Chosen to Diagram)

  from-kernel : Kernel → Diagram.ComparisonIsEquivalence
  from-kernel = Fresh.from-kernel′

  total-from-kernel : Kernel → Diagram.TotalComparisonIsEquivalence
  total-from-kernel = Fresh.total-from-kernel′

  decidable : (@♭ decB : DecEq (F.B d (F.point d)))
              (@♭ decC : DecEq (F.C d (F.point d)))
            → Diagram.ComparisonIsEquivalence
  decidable decB decC = Stable.fibres fe
    (F.B d (F.point d)) (F.C d (F.point d))
    (F.dB d (F.point d)) (F.dC d (F.point d)) decB decC
    (F.A d ∘ (λ b → F.point d , b)) (F.f d (F.point d)) reflB reflC
