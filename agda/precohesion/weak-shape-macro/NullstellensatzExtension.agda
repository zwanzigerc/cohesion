{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The Nullstellensatz as a SEPARATE extension of the basic theory.
-- Claude (Fable), 13 November 2026; fable-impl-02, HANDOFF-04 (a), (d).
--
--   unquoteDecl n = declareNullstellensatz n K
--
-- declares ONE constant  n : NAxiom K  for a closed whole-context
-- reflection K over any closed discrete base: every element of the total
-- space of K merely comes from a crisp point of the total source,
--
--   NAxiom K = (z : Total K) → Merely (Fiber θ̂ z),   θ̂ u = unit K (counit u).
--
-- Semantics: valid for every K, over every discrete base, in a model with
-- the global Nullstellensatz (FABLE-REVIEW-01 Proposition 3.2). It is also
-- DERIVABLE from the terminal instance for the total source: over a set base
-- natively (TotalBridge.relative-nullstellensatz), over a higher base by the
-- argument of RELATIVE0-HIGHER-BASE-RESEARCH-02 §3, which needs ordinary
-- truncations that this tree does not have. So a declaration for a relative
-- K is a convenience, not a new principle; the terminal declaration
-- (K : Closed X) is the axiom of the extension.
--
-- Merely A lives in Set (lsuc ℓ): it is the Church encoding with elimination
-- into propositions of level ℓ only. See GlobalPropositions for what it
-- takes to call it a proposition or to compare it with a truncation.
--
-- Nothing in the basic theory imports this module.
module NullstellensatzExtension where

open import Foundations
open import CaptureContext using (CrispUnitAt; end-at; Raise; raise)
import RelativeSliceShape as R
open R using (RelativeShapeOver)
open import GlobalPrecohesion
open import ClosedBridge using (module Existence; closed-bridge)
open import ShapeChoice using (FunExtAt)
open import GlobalDeclare using (declareStatement)
open import CaptureExplicit using (guarded)
open import Agda.Builtin.Reflection using (Name; TC; bindTC; quoteTC)

module Statement
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  (@♭ K : RelativeShapeOver Γ dΓ A) where

  -- Points to pieces for the whole context: crisp points of the total source.
  θ̂ : ♭ (Σ Γ A) → R.Output.Total K
  θ̂ u = R.Output.unit K (counit u)

  NAxiom : Set (lsuc ℓ)
  NAxiom = (z : R.Output.Total K) → Merely (Fiber θ̂ z)

-- For a closed payload this is the Nullstellensatz of the bridged shape data.
module ClosedCase
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ) (@♭ X : Set ℓ) (@♭ K : Closed X) where

  private
    open module E = Existence X K

    move : (z : T) (u : ♭ (Σ (CrispUnitAt ℓ) A)) → Statement.θ̂ K u ≡ z
         → Fiber (points-to-pieces (closed-bridge fe X K)) z
    move z (box (end-at , raise x)) e = box x , e

  closed-nullstellensatz : Statement.NAxiom K
                         → Nullstellensatz (closed-bridge fe X K)
  closed-nullstellensatz n z P P-prop k =
    n z P P-prop (λ w → k (move z (fst w) (snd w)))

open ClosedCase public using (closed-nullstellensatz)

declareNullstellensatz :
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  → Name → (@♭ K : RelativeShapeOver Γ dΓ A) → TC ⊤
declareNullstellensatz n K = guarded (
  bindTC (quoteTC (Statement.NAxiom K)) (declareStatement n))
