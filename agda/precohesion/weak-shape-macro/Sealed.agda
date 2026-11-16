{-# OPTIONS --safe --without-K --cohesion #-}

-- A seal for large derived terms. Claude (Fable), 13 November 2026;
-- fable-impl-10. Literally --safe. FABLE-IMPL-07.txt section 6 and
-- CURRENT-REFLECTION-DISPOSITION-01 item 3 ("large-term comparison").
--
--   sealed x          is x, but does not unfold outside this module
--   sealed-path x     sealed x ≡ x
--
-- Why. A relative reflection that is DERIVED through several bridges
-- (TotalConverse of DecidableBase.Fibre of a capture, say) is a large
-- term. A statement about such a reflection is cheap to check as long as
-- it is spelled in ONE way. If a client restates it in its own terms, the
-- conversion checker has to compare two spellings, normalises through all
-- the bridges, and can exhaust the heap (ExternalProductExamples in
-- fable-impl-07, ReindexingAcceptanceB in fable-impl-10). A sealed
-- reflection is opaque: the conversion checker does not unfold it. In
-- the observed cases that is what makes the restated statement
-- checkable. It is not a bound on the cost of every use.
--
-- The price. `sealed K` is only propositionally K: its carrier is not the
-- carrier of K on the nose. So seal a reflection where a result is to be
-- STATED, and keep the unsealed one where carriers and units have to be
-- identified definitionally. Both are reflections of the same family, and
-- ShapeChoice / ReindexingChoice compare them canonically.
--
-- Nothing is assumed: `abstract` is a scoping device of the language.
module Sealed where

open import Foundations

abstract
  sealed : ∀ {a} {X : Set a} → X → X
  sealed x = x

  sealed-path : ∀ {a} {X : Set a} (x : X) → sealed x ≡ x
  sealed-path x = refl
