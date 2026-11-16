{-# OPTIONS --cohesion --without-K --flat-split #-}

-- 12 November 2026, fable-impl-01: the two checks no longer use parameter
-- reconstruction; see the comment at `attempt` and FABLE-IMPL-01.txt.
--
-- A visible `instance first : CapturedShape A` is the cache seed. Fresh
-- names declared by a term macro are not in scope, so Agda's getInstances
-- cannot discover them directly. We reuse only a seed whose WHOLE slice
-- reflection has the exact, already audited payload requested by capture.
--
-- 13 November 2026, generator checkpoint after fable-impl-11 (HANDOFF-24,
-- HANDOFF-28; DIAGRAM-REUSE-DESIGN-OPTIONS-01, Option C). Two further
-- sources of candidates, each passed through the SAME `attempt`:
--   * a finite list of terms OFFERED by the caller, tried first. A
--     generator offers the completed first seed of its own call to the
--     second request, by name. Offering a term gives it nothing that a
--     visible instance of the same term would not have: it is accepted
--     only at the audited wrapper type with the audited whole payload.
--   * the two seeds of every VISIBLE instance of ClosedDiagram at the level
--     of the request (DiagramData.ClosedSeed), tried last. A bundle is
--     found by its own head; its fields are not candidates of a search at
--     CapturedShape, and the hidden auxiliary names behind a bundle are not
--     candidates of any search (probe SeedVisibility).
-- Order of trial: offered, visible CapturedShape instances, bundle seeds.
-- The first candidate that passes is used. Among independently declared
-- choices of the same payload no winner is promised, as before (R24).
--
-- 13 November 2026, step S3c after fable-impl-13 (HANDOFF-29 Q4,
-- HANDOFF-30; S3C-CAPTURED-DATA-DEPENDENCY-SEAM-01). One more source,
-- tried after the others and through the SAME `attempt`:
--   * the two REBUILT WRAPPERS of every visible instance of
--     CapturedDiagram at the level of the request,
--       CapturedField.localB d,  CapturedField.localC d.
--     A captured bundle is made inside a context, by the direct generator
--     (DeclareCapturedDiagram) or by hand; its wrappers have the bundle's
--     own context, discreteness witness, stored family, payload, point
--     and source maps. A request matches one of them only if its audited
--     wrapper type and its audited WHOLE payload type are those of that
--     wrapper, by conversion: the same source in the same context. A
--     request in a longer context does not match, nor does one for an
--     equivalent source. What is found is a name in scope with the
--     instance flag; nothing is inferred from a projection or a hidden
--     definition.
-- Order of trial now: offered, visible CapturedShape instances, seeds of
-- closed bundles, wrappers of captured bundles. Each later source is
-- queried only when the earlier ones have missed.
-- getInstances does not enumerate registrations: the compiler checks the
-- candidates against the goal and can collapse candidates that are equal
-- by conversion (it keeps the first checked candidate and drops the
-- candidates directly after it that are equal to it, under its own
-- conditions on blocked comparisons and metas; not a deduplication of
-- the whole list).
module CaptureReuse where

import CapturedShape as C
open import DiagramData
  using (ClosedDiagram; module ClosedSeed; CapturedDiagram; module CapturedField)
open import CaptureSyntax using (dropNewest)
open import CaptureExplicit using (typed; guarded)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.Sigma using (_,_)

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  h : {A : Set} → A → Arg A
  h = arg (arg-info hidden (modality relevant quantity-ω))

  candidates : Term → TC (List Term)
  candidates (meta m _) = getInstances m
  candidates _ = ret []

  -- The witness is written as syntax,
  --   whole-context (typed <wrapper type> <candidate>),
  -- and checked against the audited payload. Nothing is quoted back from the
  -- elaborated term, so neither parameter reconstruction (which can abort
  -- Agda 2.9.0-rc3, see CaptureExplicit) nor unknown syntax enters. The
  -- wrapper type and the payload are the explicit terms made by CaptureShape;
  -- dropNewest zero rejects a candidate with metas or unknowns. No checking
  -- attempt is allowed to solve the caller's metas.
  attempt : Term → Term → Term → TC (Maybe Term)
  attempt wrapperType payload candidate = runSpeculative (catchTC
    (let witness = def (quote C.Output.whole-context)
           (v (def (quote typed) (v wrapperType ∷ v candidate ∷ [])) ∷ [])
     in
     noConstraints (checkType candidate wrapperType) >>= λ _ →
     noConstraints (checkType witness payload) >>= λ checked →
     debugPrint "capture.reuse" 10 (strErr "Checked seed: " ∷ termErr checked ∷ []) >>= λ _ →
     dropNewest zero witness >>= λ closed → ret (just closed , false))
    (ret (nothing , false)))

  search : Term → Term → List Term → TC (Maybe Term)
  search wrapperType payload [] = ret nothing
  search wrapperType payload (candidate ∷ rest) =
    debugPrint "capture.reuse" 10 (strErr "Trying shape seed: " ∷ termErr candidate ∷ []) >>= λ _ →
    attempt wrapperType payload candidate >>= λ where
    (just witness) → ret (just witness)
    nothing → search wrapperType payload rest

  -- The level of the payload universe, read off the wrapper type that
  -- CaptureShape writes:  CapturedShape {a} {ℓ} A.
  payloadLevel : Term → Maybe Term
  payloadLevel (def (quote C.CapturedShape) (_ ∷ arg _ l ∷ _ ∷ [])) = just l
  payloadLevel _ = nothing

  -- Explicit syntax  ClosedSeed.seedB {ℓ} d,  ClosedSeed.seedC {ℓ} d  for
  -- each discovered bundle d. Nothing is quoted back from an elaborated
  -- term. The level is written out; the bundle is checked against
  -- ClosedDiagram ℓ as the argument of the projection.
  seedsOf : Term → List Term → List Term
  seedsOf l [] = []
  seedsOf l (d ∷ ds) =
    def (quote ClosedSeed.seedB) (h l ∷ v d ∷ []) ∷
    def (quote ClosedSeed.seedC) (h l ∷ v d ∷ []) ∷ seedsOf l ds

  bundleSeeds : Term → TC (List Term)
  bundleSeeds wrapperType with payloadLevel wrapperType
  ... | nothing = ret []
  ... | just l =
    checkType unknown (def (quote ClosedDiagram) (v l ∷ [])) >>= candidates >>= λ ds →
    ret (seedsOf l ds)

  -- Explicit syntax  CapturedField.localB {ℓ} d,  CapturedField.localC {ℓ} d
  -- for each discovered captured bundle d, as for the closed ones.
  wrappersOf : Term → List Term → List Term
  wrappersOf l [] = []
  wrappersOf l (d ∷ ds) =
    def (quote CapturedField.localB) (h l ∷ v d ∷ []) ∷
    def (quote CapturedField.localC) (h l ∷ v d ∷ []) ∷ wrappersOf l ds

  capturedWrappers : Term → TC (List Term)
  capturedWrappers wrapperType with payloadLevel wrapperType
  ... | nothing = ret []
  ... | just l =
    checkType unknown (def (quote CapturedDiagram) (v l ∷ [])) >>= candidates >>= λ ds →
    ret (wrappersOf l ds)

-- The temporary search metas and all speculative checking state are
-- discarded. An in-progress instance cannot pass the whole-payload check:
-- its context and family projections cannot reduce to the audited closed
-- input yet. The same holds for an in-progress bundle: its seeds do not
-- reduce to a wrapper before the bundle has its clause. (The direct
-- generator declares its bundle only after both of its captures.)
findShapeOffering : List Term → Term → Term → TC (Maybe Term)
findShapeOffering offered wrapperType payload = guarded (runSpeculative
  (search wrapperType payload offered >>= λ where
    (just witness) → ret (just witness , false)
    nothing →
      checkType unknown wrapperType >>= candidates >>= search wrapperType payload >>= λ where
        (just witness) → ret (just witness , false)
        nothing →
          bundleSeeds wrapperType >>= search wrapperType payload >>= λ where
            (just witness) → ret (just witness , false)
            nothing →
              capturedWrappers wrapperType >>= search wrapperType payload >>= λ result →
              ret (result , false)))

findShape : Term → Term → TC (Maybe Term)
findShape = findShapeOffering []
