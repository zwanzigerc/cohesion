{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Closed native clients of the connected-interval theorem.
-- Opus, 13 November 2026; opus-connected-interval-01, implementing
-- CONNECTED-INTERVAL-PLAN-FABLE-01.txt section 5.
--
-- Two clients, at level 0, both in the empty context:
--   Unspecified  A₀ a postulated closed type, cohesion unspecified. The
--                statement is about the codiscrete object ♯ A₀.
--   Discrete     A₀ = Bool, a closed discrete set (ClosedSliceExamples:
--                bool-set, bool-discrete). Here ʃ (♯ Bool) is the paper's
--                Π₀∇2 for the discrete base object 2.
--
-- DEPENDENCY RECORD (each client separately):
--   * four generated shape axioms, contextual-shape (0), one per `shape`
--     capture below (♯ A₀, ♯ (Two lzero), ♯ A₀ × ♯ A₀, (♯ A₀ × ♯ A₀) ×
--     ♯ (Two lzero));
--   * two generated closed product axioms (GlobalDeclare.declareProduct),
--     each for a product of two CLOSED types: instances of global finite-
--     product preservation (basic theory, T01). No product over a shared
--     crisp context is involved;
--   * one crisp hypothesis fe : FunExtAt lzero, inherited from ClosedBridge
--     (uniqueness of the bridged shape data). The theorem module
--     ConnectedInterval itself uses none;
--   * the hypothesis that ʃ (♯ 2) is contractible, as an ORDINARY module
--     parameter `connected`. It is the hypothesis of the lemma and is NOT
--     declared as an axiom: there is no schema for it and none is proposed.
--   * Unspecified only: the postulate A₀ : Set (a closed type, no axiom
--     about it).
-- No Nullstellensatz, continuity, stability, choice, large-target or
-- classifier declaration is imported or used. The product certificates
-- are closed constants and therefore crisp for free: nothing ordinary is
-- promoted to crisp.
--
-- Automatic contextual clients (plan 5.3). For a crisp VARIABLE A, `shape`
-- gives relative payloads over the packed context, not terminal shape data
-- for ♯ A; nothing in the M3 foundation turns them into such data (that
-- would be stability, which is not assumed). Over a decidable discrete
-- context DecidableBase gives terminal fibre data, but the two product
-- certificates for those fibre data are not available (converse of R36 and
-- external product capture, HANDOFF-06 item 6). So the only legitimate
-- clients today are closed ones. This is a limit of the frontend assembly,
-- not of the theorem; nothing here postulates products in slices or
-- relabels a contextual fibre as ShapeData.
module ConnectedIntervalExamples where

open import Foundations
open import Agda.Builtin.Bool
open import NativeSharp using (♯)
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import ClosedBridge using (closed-bridge)
open import GlobalPrecohesion using (ShapeData; ʃ; Merely; Closed)
open import GlobalDeclare using (declareProduct; module ProductStatement)
open import ConnectedIntervalNative using (Two)
open import ConnectedInterval using (module Modal)

------------------------------------------------------------------------
-- Client 1: a closed type of unspecified cohesion.

module Unspecified where

  postulate A₀ : Set

  X₀ J₀ Z₀ W₀ : Set
  X₀ = ♯ A₀
  J₀ = ♯ (Two lzero)
  Z₀ = X₀ × X₀
  W₀ = Z₀ × J₀

  -- Four generated shape axioms.
  sX : CapturedShape X₀
  sX = shape

  sJ : CapturedShape J₀
  sJ = shape

  sZ : CapturedShape Z₀
  sZ = shape

  sW : CapturedShape W₀
  sW = shape

  KX : Closed X₀
  KX = C.Output.whole-context sX

  KJ : Closed J₀
  KJ = C.Output.whole-context sJ

  KZ : Closed Z₀
  KZ = C.Output.whole-context sZ

  KW : Closed W₀
  KW = C.Output.whole-context sW

  -- Two generated closed product axioms.
  unquoteDecl pZ = declareProduct pZ KX KX KZ
  unquoteDecl pW = declareProduct pW KZ KJ KW

  module Client (@♭ fe : FunExtAt lzero) where

    dX : ShapeData X₀
    dX = closed-bridge fe X₀ KX

    dJ : ShapeData J₀
    dJ = closed-bridge fe J₀ KJ

    dZ : ShapeData Z₀
    dZ = closed-bridge fe Z₀ KZ

    dW : ShapeData W₀
    dW = closed-bridge fe W₀ KW

    module M = Modal A₀ dX dJ dZ dW (ProductStatement.preserves KZ KJ KW fe pW)

    coaugmentation : A₀ → ʃ dX
    coaugmentation = M.coaugmentation

    module _ (connected : IsContr (ʃ dJ)) where

      private
        module R = M.Conclusion (ProductStatement.preserves KX KX KZ fe pZ) connected

      lemma-3-4 : IsProp (ʃ dX)
      lemma-3-4 = R.shape-is-prop

      inhabited : Merely A₀ → IsContr (ʃ dX)
      inhabited = R.inhabited-contractible

------------------------------------------------------------------------
-- Client 2: the closed discrete set Bool.

module Discrete where

  X₀ J₀ Z₀ W₀ : Set
  X₀ = ♯ Bool
  J₀ = ♯ (Two lzero)
  Z₀ = X₀ × X₀
  W₀ = Z₀ × J₀

  -- Four generated shape axioms.
  sX : CapturedShape X₀
  sX = shape

  sJ : CapturedShape J₀
  sJ = shape

  sZ : CapturedShape Z₀
  sZ = shape

  sW : CapturedShape W₀
  sW = shape

  KX : Closed X₀
  KX = C.Output.whole-context sX

  KJ : Closed J₀
  KJ = C.Output.whole-context sJ

  KZ : Closed Z₀
  KZ = C.Output.whole-context sZ

  KW : Closed W₀
  KW = C.Output.whole-context sW

  -- Two generated closed product axioms.
  unquoteDecl pZ = declareProduct pZ KX KX KZ
  unquoteDecl pW = declareProduct pW KZ KJ KW

  module Client (@♭ fe : FunExtAt lzero) where

    dX : ShapeData X₀
    dX = closed-bridge fe X₀ KX

    dJ : ShapeData J₀
    dJ = closed-bridge fe J₀ KJ

    dZ : ShapeData Z₀
    dZ = closed-bridge fe Z₀ KZ

    dW : ShapeData W₀
    dW = closed-bridge fe W₀ KW

    module M = Modal Bool dX dJ dZ dW (ProductStatement.preserves KZ KJ KW fe pW)

    coaugmentation : Bool → ʃ dX
    coaugmentation = M.coaugmentation

    module _ (connected : IsContr (ʃ dJ)) where

      private
        module R = M.Conclusion (ProductStatement.preserves KX KX KZ fe pZ) connected

      -- Π₀∇2 is a proposition.
      lemma-3-4 : IsProp (ʃ dX)
      lemma-3-4 = R.shape-is-prop

      -- Bool is inhabited, so Π₀∇2 is contractible. The Merely witness is
      -- the Church eliminator applied to an actual point; nothing is chosen.
      contractible : IsContr (ʃ dX)
      contractible = R.inhabited-contractible (λ P P-prop k → k true)
