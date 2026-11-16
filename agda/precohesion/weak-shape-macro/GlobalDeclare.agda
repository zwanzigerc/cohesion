{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The closed finite-product axiom of the basic theory, as a declaration
-- schema. Claude (Fable), 13 November 2026; fable-impl-02, HANDOFF-04 (a).
--
--   unquoteDecl p = declareProduct p K_X K_Y K_XY
--
-- declares ONE constant
--
--   p : ProductAxiom K_X K_Y K_XY
--
-- for three closed payloads K_X : Closed X, K_Y : Closed Y, K_XY :
-- Closed (X × Y), i.e. for three constants that `shape` declared in the
-- empty context. ProductAxiom says that the CANONICAL comparison built from
-- the three actual units is an equivalence. Its statement uses only
-- ClosedBridge.Existence: no function extensionality occurs in the type.
--
-- What the schema refuses, and why:
--   * any non-empty context. A product of two families over one shared
--     context is a fibre product over that context, and its preservation is
--     false in the finite-group model (sign-kernel square).
--   * payloads that are not closed. This is a type error: the arguments
--     must have type  Closed _ , and a capture formed in a non-empty context
--     has a payload over the packed context.
-- The nullary case is a theorem (GlobalPrecohesion.shape-of-unit) and has no
-- declaration.
--
-- This module is part of the BASIC theory (T01). The Nullstellensatz is not:
-- it is declared by NullstellensatzExtension, which nothing here imports.
module GlobalDeclare where

open import Foundations
import RelativeSliceShape as R
open import GlobalPrecohesion
open import ClosedBridge using (module Existence; module Bridge; closed-bridge)
open import ShapeChoice using (FunExtAt)
open import CaptureExplicit using (explicit; guarded)
open import Agda.Builtin.Reflection as Refl
  using (Name; Term; TC; Arg; arg; arg-info; visible; modality; relevant;
         quantity-ω; bindTC; returnTC; typeError; strErr; getContext;
         inContext; Telescope; quoteTC; inferType; declarePostulate)
open import Agda.Builtin.List using ([]; _∷_)

------------------------------------------------------------------------
-- The statement.

module ProductStatement
  {@♭ ℓ : Level} {@♭ X Y : Set ℓ}
  (@♭ KX : Closed X) (@♭ KY : Closed Y) (@♭ KXY : Closed (X × Y)) where

  private
    module EX = Existence X KX
    module EY = Existence Y KY
    module EXY = Existence (X × Y) KXY

  first₀ : EXY.T → EX.T
  first₀ = EXY.Target.rec₀ EX.T EX.T-set (R.Output.total-discrete KX)
    (λ p → EX.η₀ (fst p))

  second₀ : EXY.T → EY.T
  second₀ = EXY.Target.rec₀ EY.T EY.T-set (R.Output.total-discrete KY)
    (λ p → EY.η₀ (snd p))

  -- The canonical comparison of the three actual payloads.
  compare₀ : EXY.T → EX.T × EY.T
  compare₀ z = first₀ z , second₀ z

  compare₀-η : (x : X) (y : Y) → compare₀ (EXY.η₀ (x , y)) ≡ (EX.η₀ x , EY.η₀ y)
  compare₀-η x y = pair-path
    (EXY.Target.rec₀-η EX.T EX.T-set (R.Output.total-discrete KX)
      (λ p → EX.η₀ (fst p)) (x , y))
    (EXY.Target.rec₀-η EY.T EY.T-set (R.Output.total-discrete KY)
      (λ p → EY.η₀ (snd p)) (x , y))

  ProductAxiom : Set ℓ
  ProductAxiom = IsEquiv compare₀

  -- For the shape data that ClosedBridge makes from the same payloads, this
  -- is PreservesProduct on the nose: the two comparisons are the same term.
  preserves : (@♭ fe : FunExtAt ℓ) → ProductAxiom
            → PreservesProduct (closed-bridge fe X KX) (closed-bridge fe Y KY)
                               (closed-bridge fe (X × Y) KXY)
  preserves fe p = p

------------------------------------------------------------------------
-- The declaration.

private
  infixl 1 _>>=_
  _>>=_ = bindTC

  v : {A : Set} → A → Arg A
  v = arg (arg-info visible (modality relevant quantity-ω))

  -- Shared by the declaration schemas for closed statements: empty context,
  -- parameters written out without Agda's reconstruction, one postulate.
  open-context : TC ⊤
  open-context = typeError
    (strErr "A global precohesion axiom is a closed statement about closed shapes and can only be declared in the empty context. Inside a parameterised module or definition it would become a statement over that context: for products that is a fibre product over a shared base, which shape need not preserve. Declare it at top level and use it here." ∷ [])

  -- A check only: it declares nothing.
  both-empty : Telescope → Telescope → TC ⊤
  both-empty [] [] = returnTC tt
  both-empty _ _ = open-context

  -- The only definition of this module that contains a declaring
  -- primitive. It fixes the reflection flags and checks both the context
  -- of the calling declaration (which is what declarePostulate abstracts
  -- over) and the current one, in this same definition, before the
  -- primitive is reached (fable-impl-04; FRONTEND-M3-AUDIT-01 section 1).
  declareClosedStatement : Name → Term → TC ⊤
  declareClosedStatement n statement = guarded (
    inContext [] getContext >>= λ calling →
    getContext >>= λ current →
    both-empty calling current >>= λ _ →
    inferType statement >>= λ sort →
    explicit sort statement >>= λ written →
    declarePostulate (v n) written)

-- TRUSTED EXTENSION SURFACE (FABLE-REVIEW-03.txt section 3). This program
-- postulates the closed statement it is given. It checks that the statement
-- is a closed, well-formed type in the empty context, and nothing about
-- what the statement says: whoever calls it adds an axiom and answers for
-- its validity. In this tree it is called by NullstellensatzExtension
-- (declareNullstellensatz) and by LargeTargetDeclare (declareLargeUP); the
-- semantic justification of each statement is given where it is defined.
declareStatement : Name → Term → TC ⊤
declareStatement = declareClosedStatement

declareProduct : {@♭ ℓ : Level} {@♭ X Y : Set ℓ} → Name
               → (@♭ KX : Closed X) (@♭ KY : Closed Y) (@♭ KXY : Closed (X × Y))
               → TC ⊤
declareProduct n KX KY KXY = guarded (
  quoteTC (ProductStatement.ProductAxiom KX KY KXY) >>= declareClosedStatement n)
