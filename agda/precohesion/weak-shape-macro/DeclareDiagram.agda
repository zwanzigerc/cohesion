{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A declaration-position generator for CLOSED diagrams: one public name,
-- at most two new shape axioms. Claude (Fable), 13 November 2026;
-- generator checkpoint after fable-impl-11 (HANDOFF-24, HANDOFF-28).
-- PROTOTYPE for the registration design (DIAGRAM-REUSE-DESIGN-OPTIONS-01,
-- Option C). It is the closed-curried intermediate step, not the direct
-- open-context frontend.
--
-- Use, at top level:
--   unquoteDecl cells =
--     declareClosedDiagram cells dB B-set dC C-set f A
-- where f : C → B, A : B → Set ℓ and the evidence are the user's native
-- typed terms. The result is  instance cells : ClosedDiagram ℓ,  whose
-- eight data fields are those terms and whose two payloads are the whole
-- payloads of captures of  Σ B A  and  Σ C (A ∘ f).
--
-- WHAT IT DOES, in order.
--   1. Both the context of the calling declaration and the current
--      context must be empty.
--   2. The first capture: lookup, or ONE new axiom. Its wrapper is
--      completed as an ordinary definition under a fresh name
--      (DeclareCapturedShape.declareSeed).
--   3. The second capture, with the first seed's name offered to the
--      matcher. If the two audited payloads coincide the first choice is
--      used and no second axiom is declared.
--   4. The public name is declared as an INSTANCE of ClosedDiagram ℓ and
--      defined as the constructor applied to the eight terms and the two
--      payloads.
--   5. Native final check: Agda checks the DIRECT constructor
--        generated KB KC
--      at the type
--        ClosedDiagramOf dB B-set dC C-set f A <the public name>
--      formed from the user's own typed arguments, KB and KC being the
--      two payloads. Checking that term forces the stored fields to be
--      the native inputs by conversion, whatever reflected syntax did to
--      them on the way; if they are not, the whole declaration fails.
--
-- WHAT IS AND IS NOT REGISTERED. The two seed names are fresh, hence not
-- in source scope, hence not candidates of any instance search. Only the
-- public bundle is registered. A later request, by `shape`, declareShape
-- or this generator, finds the bundle by its head and tries its two
-- seeds through the matcher of CaptureReuse. All of step 2 and 3's
-- lookups go the same way, so a prior visible seed or bundle is reused
-- here as well.
--
-- The generator has no AXIOM-declaring primitive of its own: every shape
-- postulate of a call is emitted by CaptureShape, through the unchanged
-- audited capture. Its own declarations are definitions (declareDef and
-- defineFun for the public bundle here; the two wrappers in
-- DeclareCapturedShape.declareSeed). Every axiom that capture declares
-- for a call occurs in the public bundle of that call; if any later
-- step fails, the declaration fails as a whole.
module DeclareDiagram where

open import Foundations
import CapturedShape as C
open import GlobalPrecohesion using (Closed)
open import DiagramData
open import DeclareCapturedShape using (declareSeed)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Unit using (tt)

private
  infixl 1 _>>=_
  _>>=_ = bindTC
  ret = returnTC

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  inst : {A : Set} → A → Arg A
  inst = arg (arg-info instance′ (modality relevant quantity-ω))

  both-empty : Telescope → Telescope → TC ⊤
  both-empty [] [] = ret tt
  both-empty _ _ = typeError
    (strErr "declareClosedDiagram declares a CLOSED diagram and must be used at top level, outside every module with parameters and every local context. A diagram over a context is given as closed curried families." ∷ [])

  -- The whole payload of a completed seed, as syntax.
  payloadOf : Name → Term
  payloadOf seed = def (quote C.Output.whole-context) (v (def seed []) ∷ [])

declareClosedDiagram : {@♭ ℓ : Level} → Name → {@♭ B C : Set ℓ}
  → (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
  → (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
  → (@♭ f : C → B) (@♭ A : B → Set ℓ) → TC ⊤
declareClosedDiagram {ℓ} n {B} {C} dB B-set dC C-set f A = guarded (
  inContext [] getContext >>= λ calling →
  getContext >>= λ current →
  both-empty calling current >>= λ _ →
  freshName "diagram-seed-B" >>= λ seedB →
  declareSeed {a = ℓ} {ℓ = ℓ} [] seedB (Σ B A) >>= λ _ →
  freshName "diagram-seed-C" >>= λ seedC →
  declareSeed {a = ℓ} {ℓ = ℓ} (def seedB [] ∷ []) seedC (Σ C (A ∘ f)) >>= λ _ →
  quoteTC (ClosedDiagram ℓ) >>= λ type →
  quoteTC B >>= λ B′ → quoteTC C >>= λ C′ →
  quoteTC dB >>= λ dB′ → quoteTC B-set >>= λ B-set′ →
  quoteTC dC >>= λ dC′ → quoteTC C-set >>= λ C-set′ →
  quoteTC f >>= λ f′ → quoteTC A >>= λ A′ →
  declareDef (inst n) type >>= λ _ →
  defineFun n (clause [] []
    (con (quote closed-diagram)
      (v B′ ∷ v C′ ∷ v dB′ ∷ v B-set′ ∷ v dC′ ∷ v C-set′ ∷ v f′ ∷ v A′
       ∷ v (payloadOf seedB) ∷ v (payloadOf seedC) ∷ [])) ∷ []) >>= λ _ →
  unquoteTC {A = ClosedDiagram ℓ} (def n []) >>= λ d →
  unquoteTC {A = ClosedDiagramOf dB B-set dC C-set f A d}
    (con (quote generated) (v (payloadOf seedB) ∷ v (payloadOf seedC) ∷ [])) >>= λ _ →
  ret tt)
