{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The product law for FRESH captures in an open crisp context, from one
-- closed product axiom. fable-impl-07; HANDOFF-06 item 6 (product assembly
-- over a decidable discrete context).
--
-- In the context of a crisp b : Bool, OpenContextExamples captures the
-- shapes of  Family b,  ReindexedFamily b  and of their product, and derives
-- terminal shape data t₁, t₂, t₁₂ of the three types at the current point.
-- Whether the canonical comparison of t₁, t₂, t₁₂ is invertible was left
-- there as a hypothesis. Here it is PROVED, for every crisp b, from:
--
--   three closed captures: of the total spaces  X₁ = Σ Bool Family,
--   X₂ = Σ Bool ReindexedFamily,  and of  X₁ × X₂;
--   ONE closed product axiom, for these three (declareProduct).
--
-- The route: ClosedBridge (shape data of the totals), ExternalProduct (the
-- fibres over (b , b) of the external product satisfy the product law, and
-- the law does not depend on the choice of the three shape data, so it
-- passes to the data of the fresh captures: product-for).
--
-- No product axiom is declared for a fibre or in a context; none is
-- declared for Family b. No Nullstellensatz, no continuity, no stability.
-- The result is a term in closed constants and crisp variables, so it can be
-- used where a crisp product certificate is required (`crisp-use`).
--
-- Import note. OpenContextExamples and ClosedSliceExamples are imported for
-- their captures, bool-dec and the closed family. They bring their own
-- earlier declarations into the import closure of this file; the proof
-- below uses none of them except the three captures in the context of b.
module ExternalProductExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import ClosedBridge using (closed-bridge)
open import GlobalDeclare
open import ClosedSliceExamples
  using (Family; ReindexedFamily; bool-discrete; bool-set)
open import DecidableBase
import OpenContextExamples as Open
open Open using (bool-dec)
open import ExternalProduct

------------------------------------------------------------------------
-- Closed side: three captures in the empty context and one product axiom.

X₁ : Set
X₁ = Σ Bool Family

X₂ : Set
X₂ = Σ Bool ReindexedFamily

captured₁ : CapturedShape X₁
captured₁ = shape

captured₂ : CapturedShape X₂
captured₂ = shape

captured₁₂ : CapturedShape (X₁ × X₂)
captured₁₂ = shape

KX₁ : Closed X₁
KX₁ = C.Output.whole-context captured₁

KX₂ : Closed X₂
KX₂ = C.Output.whole-context captured₂

KX₁₂ : Closed (X₁ × X₂)
KX₁₂ = C.Output.whole-context captured₁₂

unquoteDecl totals-product = declareProduct totals-product KX₁ KX₂ KX₁₂

------------------------------------------------------------------------
-- Open side: the fresh captures of OpenContextExamples, in the context of b.

module Assembly (@♭ fe : FunExtAt lzero) (@♭ b : Bool) where

  private
    s₁ : ShapeData X₁
    s₁ = closed-bridge fe X₁ KX₁

    s₂ : ShapeData X₂
    s₂ = closed-bridge fe X₂ KX₂

    s₁₂ : ShapeData (X₁ × X₂)
    s₁₂ = closed-bridge fe (X₁ × X₂) KX₁₂

    totals : PreservesProduct s₁ s₂ s₁₂
    totals = ProductStatement.preserves KX₁ KX₂ KX₁₂ fe totals-product

    module E = External fe {dΓ₁ = bool-discrete} {dΓ₂ = bool-discrete}
                 bool-set bool-set s₁ s₂ s₁₂
    module P = E.AtPoint bool-dec bool-dec b b

  -- The data of the fresh captures at the current point.
  open Open.Open fe b using () renaming (d₁ to t₁; d₂ to t₂; d₁₂ to t₁₂)

  -- The product law for the fresh captures: the fibres of the external
  -- product over (b , b) satisfy it, and it does not depend on the choice
  -- of the three shape data.
  open-product : PreservesProduct t₁ t₂ t₁₂
  open-product = P.product-for totals t₁ t₂ t₁₂

  -- It discharges the hypothesis that OpenContextExamples.Consumer left
  -- open: with the Nullstellensatz for the two factors, the Nullstellensatz
  -- for the captured product.
  module WithPoints
    (points₁ : Nullstellensatz t₁) (points₂ : Nullstellensatz t₂) where

    points₁₂ : Nullstellensatz t₁₂
    points₁₂ = product-nullstellensatz t₁ t₂ t₁₂ open-product points₁ points₂

  -- The certificate is available crisply: it is built from closed constants
  -- and the crisp variables fe and b.
  private
    crisp-consumer : (@♭ c : PreservesProduct t₁ t₂ t₁₂) → IsEquiv (compare t₁ t₂ t₁₂)
    crisp-consumer c = c

  crisp-use : IsEquiv (compare t₁ t₂ t₁₂)
  crisp-use = crisp-consumer open-product
