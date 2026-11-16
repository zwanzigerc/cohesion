{-# OPTIONS --cohesion --without-K --flat-split #-}

-- fable-impl-03: the exported check fixes the reflection flags itself
-- (`guarded`); the per-variable check is private. FABLE-REVIEW-03.txt §1.
module CaptureCrispCheck where

open import Foundations using (box)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection as R
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

private
  vArg : {A : Set} → A → Arg A
  vArg = arg (arg-info visible (modality relevant quantity-ω))

  -- ArgInfo in Agda 2.8 does not expose cohesion. Ask the actual checker
  -- whether this variable can be passed to a crisp argument instead. Restore
  -- speculative state so checking never solves the caller's metavariables.
  -- Also reject variable types whose internal modalities cannot survive the
  -- reflection API's type roundtrip (notably a nested crisp Pi binder).
  checkCrispVariable : Nat → TC ⊤
  checkCrispVariable i = runSpeculative
    (bindTC (noConstraints (inferType (var i []))) λ variableType →
     bindTC (noConstraints (checkType (var i []) variableType)) λ _ →
     bindTC (noConstraints (inferType (con (quote box) (vArg (var i []) ∷ []))))
       λ _ → returnTC (tt , false))

  checkEntries : Nat → Telescope → TC ⊤
  checkEntries i [] = returnTC tt
  checkEntries i ((_ , arg (arg-info _ (modality relevant quantity-ω)) _) ∷ rest) =
    bindTC (checkCrispVariable i) λ _ → checkEntries (suc i) rest
  checkEntries i (_ ∷ _) = typeError
    (strErr "Automatic shape capture requires relevant, unerased crisp variables." ∷ [])

-- Every variable of the current context is crisp, relevant and unerased.
-- It reads the context and asks the checker, so it fixes the reflection
-- flags before its first primitive; it changes no state and declares
-- nothing.
checkCrispContext : TC ⊤
checkCrispContext = guarded (bindTC getContext (checkEntries zero))

macro
  -- Diagnostic entry point: accepted exactly where the context check of
  -- the capture macros succeeds.
  check-crisp-context : Term → TC ⊤
  check-crisp-context hole = guarded (bindTC checkCrispContext λ _ →
    unify hole (con (quote tt) []))
