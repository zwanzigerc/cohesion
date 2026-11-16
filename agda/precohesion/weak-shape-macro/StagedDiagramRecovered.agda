{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The reader on an index whose reflected syntax DROPS PARAMETERS.
-- Claude (Fable), 13 November 2026; after fable-impl-14
-- (S3-METADATA-STAGING-PREFLIGHT-01 section 3: recovery of implicit
-- arguments by the accepted explicit machinery). No staging here.
--
-- The diagram is case Recovered of DeclareCapturedDiagramExamples: the
-- map is a projection given as a function, and the family has pairs
-- inside and uses the variable of the context. The type of the
-- descriptor, as reflection returns it, has constructors and a
-- projection without their parameters. The audit writes them out again
-- (CaptureExplicit, through CaptureShape.auditPacked), and the original
-- name is then checked at the candidate type as in every other case.
--
-- DECLARATIONS OF THIS FILE: the shapes of the one generator call, in the
-- context. The reader declares a definition.
module StagedDiagramRecovered where

open import Foundations
open import Agda.Builtin.Bool
open import Agda.Builtin.List using (List; []; _∷_)
open import CaptureContext using (pair; end-at)
open import BoolDecidable using (bool-dec; bool-is-set; bool-is-discrete)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalChoice using (×-set)
open import DiagramBundle
open import DiagramMetadata
open import DeclareCapturedDiagram
open import ReadCapturedDiagram

module Recovered (@♭ b : Bool) where

  unquoteDecl cells descriptor =
    declareStagedDiagram cells descriptor (bool-dec ∷ [])
      bool-is-discrete bool-is-set
      (SigmaDiscrete.discrete bool-is-discrete (λ _ → bool-is-discrete))
      (×-set bool-is-set bool-is-set)
      fst (λ x → (x , b) ≡ (true , false))

unquoteDecl index = readCapturedDiagram index (quote Recovered.descriptor)

linked : CrispPi Bool (λ b → CapturedDiagramFor index)
linked = Recovered.descriptor

module _ (@♭ b : Bool) where

  map-is : MetaField.f index (pair b end-at) ≡ fst
  map-is = refl

  family-is : FibreAt (MetaField.A index) (pair b end-at)
            ≡ (λ x → (x , b) ≡ (true , false))
  family-is = refl

  same-metadata : metadata (Recovered.cells b) ≡ index
  same-metadata = refl
