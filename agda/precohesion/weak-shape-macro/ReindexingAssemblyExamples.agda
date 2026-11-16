{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The two forms of the conclusion, at an actual closed diagram.
-- fable-impl-08; FABLE-REVIEW-05 section 4, fields A4 to A7.
--
-- ShapeReindexingExamples declares two closed relative reflections over
-- Bool: `original` of Family, and `after-collapse` of Family ∘ collapse for
-- the constant map collapse : Bool → Bool, and forms their canonical
-- comparison. This file declares NOTHING. It shows what a client of a
-- proof about whole objects receives: from the statement that the total
-- comparison is an equivalence, the statement in fibre form for the SAME
-- canonical comparison, and conversely.
--
-- Neither statement is asserted or proved here: both functions below are
-- conversions between two hypotheses. (fable-impl-10, HANDOFF-18
-- correction 2: an earlier comment said that the comparison of this
-- diagram need not be invertible. That was wrong. The bases are Bool, and
-- over bases with decidable equality the comparison is invertible in the
-- weak core with function extensionality: DecidableReindexing, and module
-- Derived of ReindexingAcceptanceA. This file tests the conversions, not a
-- diagram that could be unstable.)
--
-- Import note. ShapeReindexingExamples brings its own declarations, and
-- those of RelativeGenericExamples and ClosedSliceExamples, into the import
-- closure. Only `original`, `after-collapse` and `collapse` are used.
module ReindexingAssemblyExamples where

open import Foundations
open import RelativeSliceShape
open import Agda.Builtin.Bool
open import ClosedSliceExamples using (Family; bool-discrete; bool-set)
import ShapeReindexingExamples as Earlier
open Earlier using (collapse; original; after-collapse)
open import ReindexingAssembly

module Collapse = TotalForm Bool Bool bool-discrete bool-discrete
  Family collapse original after-collapse

-- Total form ⇒ fibre form. Bool is a set.
from-total : Collapse.TotalComparisonIsEquivalence
           → Collapse.ComparisonIsEquivalence
from-total = Collapse.FromTotal.fibres bool-set

-- Fibre form ⇒ total form.
to-total : Collapse.ComparisonIsEquivalence
         → Collapse.TotalComparisonIsEquivalence
to-total = Collapse.FromFibres.total

-- The comparison in both statements is the one that ShapeReindexing
-- constructs and ShapeReindexingExamples names, on the nose, and it has
-- that module's unit law.
same-comparison : (b : Bool) (w : Output.family after-collapse b)
                → Collapse.comparison b w ≡ Earlier.boolean-comparison b w
same-comparison b w = refl

unit-law : (b : Bool) (a : Family (collapse b))
         → Collapse.comparison b (Output.family-unit after-collapse b a)
           ≡ Output.family-unit original (collapse b) a
unit-law = Collapse.comparison-on-unit
