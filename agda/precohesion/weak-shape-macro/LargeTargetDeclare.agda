{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Large targets as a SEPARATE extension: one declaration schema.
-- Claude (Fable), 13 November 2026; fable-impl-03, HANDOFF-06 item 5.
--
--   unquoteDecl c = declareLargeUP c L X K
--
-- declares ONE constant
--
--   c : ClosedLargeUP L X K
--     = LargeTerminalUP L X (Existence.T X K) (Existence.η₀ X K)
--
-- for a closed X : Set a, a closed payload K : Closed X (a constant that
-- `shape` declared in the empty context) and an explicit level L. It says
-- that precomposition with the unit that K ALREADY has is an equivalence on
-- crisp maps into every discrete set of Set (a ⊔ L). Nothing is chosen:
-- the carrier and the unit are those of K, and they do not depend on
-- function extensionality (ClosedBridge.Existence). The constant can
-- therefore be declared before any extensionality hypothesis is in scope
-- and used under every such hypothesis (`attach`).
--
-- What the type records: X, K (hence carrier and unit), the source level a
-- and the ceiling a ⊔ L. What the schema refuses, and how:
--   * a non-empty context: GlobalDeclare's declaring program;
--   * a payload that is not closed: a type error, the argument must have
--     type Closed X;
--   * a certificate used at another payload or at a larger ceiling: a type
--     error, they are different types. A larger ceiling restricts to a
--     smaller one by LargeTarget.Restrict; there is no map the other way.
--
-- Semantics (FABLE-REVIEW-03.txt section 5): valid for a closed K in a
-- model given by a genuine adjunction whose reflection of the closed X is
-- small, with the independent-product reading of crisp stages. It is NEW
-- trusted data, not a consequence of K or of ShapeData at level a. It does
-- not make a relative shape over a larger context small, and it says
-- nothing about Merely, the Nullstellensatz or continuity.
--
-- Nothing in the basic theory or in NullstellensatzExtension imports this
-- module.
module LargeTargetDeclare where

open import Foundations
open import GlobalPrecohesion using (Closed)
open import ClosedBridge using (module Existence; module Bridge)
open import ShapeChoice using (FunExtAt)
open import LargeTarget using (LargeTerminalUP; LargeOn)
open import GlobalDeclare using (declareStatement)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection using (Name; TC; bindTC; quoteTC)

ClosedLargeUP : {@♭ a : Level} (@♭ L : Level) (@♭ X : Set a) (@♭ K : Closed X)
              → Set (lsuc (a ⊔ L))
ClosedLargeUP L X K = LargeTerminalUP L X (Existence.T X K) (Existence.η₀ X K)

-- The same certificate, for the shape data that ClosedBridge makes from K
-- with ANY function extensionality at level a. The definition is the
-- identity: carrier and unit of Bridge.data-of fe X K are T and η₀.
attach : {@♭ a : Level} (@♭ L : Level) (@♭ X : Set a) (@♭ K : Closed X)
       → (@♭ c : ClosedLargeUP L X K)
       → (@♭ fe : FunExtAt a) → LargeOn L (Bridge.data-of fe X K)
attach L X K c fe = c

declareLargeUP : {@♭ a : Level} → Name
               → (@♭ L : Level) (@♭ X : Set a) (@♭ K : Closed X) → TC ⊤
declareLargeUP n L X K = guarded (
  bindTC (quoteTC (ClosedLargeUP L X K)) (declareStatement n))
