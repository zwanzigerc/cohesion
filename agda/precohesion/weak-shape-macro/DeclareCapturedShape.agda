{-# OPTIONS --cohesion --without-K --flat-split #-}

-- 12 November 2026, fable-impl-01: declared type and body are the explicit
-- terms returned by CaptureShape.captureCore; no parameter reconstruction.
--
-- A declaration-position frontend can give Agda a visible name and mark
-- it as an instance. The ordinary term macro cannot bring its fresh hidden
-- declaration into scope. The source is a native typed argument, not raw
-- reflected syntax, so final unquotation retains its cohesion annotations.
--
-- 13 November 2026, generator checkpoint after fable-impl-11 (HANDOFF-28,
-- S2-PREFLIGHT-SEED-COMPLETION-01): the one flow below also serves
-- declareSeed, for a generator that completes a wrapper under a name of
-- its own before it offers that name to a later capture of the same call.
-- declareShape is that flow with no offered term and the instance flag,
-- as before.
module DeclareCapturedShape where

open import Foundations using (Level)
open import CapturedShape using (CapturedShape)
open import CaptureShape using (captureCoreOffering; explicit-only)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Sigma using (_,_)

private
  infixl 1 _>>=_
  _>>=_ = bindTC

  -- An instance when the name is one that source scope can see; an
  -- ordinary definition otherwise.
  named : {A : Set} → Bool → A → Arg A
  named true = arg (arg-info instance′ (modality relevant quantity-ω))
  named false = arg (arg-info visible (modality relevant quantity-ω))

  declareWith : {@♭ a ℓ : Level} → Bool → List Term → Name → (@♭ A : Set a) → TC ⊤
  declareWith {ℓ = ℓ} registered offered n A = guarded (
    quoteTC (CapturedShape {ℓ = ℓ} A) >>= λ wrapperType →
    checkType unknown wrapperType >>= λ hole →
    captureCoreOffering offered explicit-only hole >>= λ where
      (declaredType , value) →
        unify hole value >>= λ _ →
        -- This check uses the ORIGINAL native type, rather than its lossy
        -- reflected image. In particular, a crisp Pi binder cannot silently
        -- become ordinary.
        unquoteTC {A = CapturedShape {ℓ = ℓ} A} hole >>= λ _ →
        -- Declared type and body are the explicit terms made by the capture;
        -- nothing is quoted back with parameter reconstruction (which can
        -- abort Agda 2.9.0-rc3; see CaptureExplicit).
        declareDef (named registered n) declaredType >>= λ _ →
        defineFun n (clause [] [] value ∷ []))

-- Use: unquoteDecl first = declareShape first A
-- Both universe parameters are inferred; capture determines the output
-- universe from the whole native context, just as for the typed term macro.
declareShape : {@♭ a ℓ : Level} → Name → (@♭ A : Set a) → TC ⊤
declareShape {a} {ℓ} = declareWith {a} {ℓ} true []

-- For a generator. The name is the caller's own (normally fresh, hence not
-- in source scope): it is declared as an ORDINARY definition, since an
-- instance flag on a name outside scope registers nothing that a search
-- can find. `offered` is the finite list of earlier completed seeds of the
-- same call, each written as its name applied to nothing: the capture
-- tries them, through the unchanged matcher, before the visible instances.
-- When this returns, the wrapper is a complete definition, and its name
-- is syntax without a placeholder that can in turn be offered.
declareSeed : {@♭ a ℓ : Level} → List Term → Name → (@♭ A : Set a) → TC ⊤
declareSeed {a} {ℓ} = declareWith {a} {ℓ} false
