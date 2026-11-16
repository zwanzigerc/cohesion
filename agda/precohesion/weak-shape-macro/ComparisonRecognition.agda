{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Recognising the canonical reindexing comparison. Postulate-free.
-- Claude (Fable), 13 November 2026; fable-impl-10.
--
-- Let Γ be discrete, Γ′ a discrete SET, f : Γ′ → Γ, A a family over Γ, K a
-- relative reflection of A, and d terminal shape data of the total source
-- Σ Γ′ (A ∘ f). TotalConverse makes d a relative reflection over Γ′
-- (`reflection`), and ShapeReindexing gives the canonical comparison
--
--     comparison-total : ʃ d → Pullback (projection K) f.
--
--   Recognise.canonical   every crisp map θ : ʃ d → Pullback (projection K) f
--                         that sends the unit of d to the pulled-back unit
--                         of K is the canonical comparison, pointwise
--   Recognise.total       if such a θ is an equivalence, the canonical
--                         comparison is one
--
-- Proof: uniqueness for d at the target Pullback (projection K) f, which
-- is a discrete set because Γ′ is a set and K has set fibres.
--
-- Why this module exists. It is the tool for showing that a comparison is
-- invertible when an explicit inverse-carrying description of the pulled-
-- back total space is at hand (DecidableRestriction). It is stated for an
-- ABSTRACT d on purpose: with d a variable the universal property of
-- `reflection` does not unfold, so the unit law of the comparison is
-- checked cheaply. Stating the same lemma directly for data produced by
-- several bridges made the conversion checker normalise through all of
-- them (FABLE-IMPL-10.txt, section on cost). Nothing here says that a
-- comparison is invertible without such a θ.
module ComparisonRecognition where

open import Foundations
open import RelativeSliceShape
open import ShapeChoice using (FunExtAt)
open import Adjointify using (quasi-inverse)
open import GlobalPrecohesion
open import TotalBridge using (Σ-set)
open import TotalConverse using (module Converse)
open import ReindexingAssembly using (module TotalForm)

module Recognise
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Γ Γ′ : Set ℓ)
  (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
  (@♭ Γ′-set : IsSet Γ′)
  (@♭ A : Γ → Set ℓ) (@♭ f : Γ′ → Γ)
  (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ d : ShapeData (Σ Γ′ (A ∘ f))) where

  -- The relative reflection over Γ′ with the carrier and unit of d.
  reflection : RelativeShapeOver Γ′ dΓ′ (A ∘ f)
  reflection = Converse.relative fe {dΓ = dΓ′} Γ′-set {A = A ∘ f} d

  module Form = TotalForm Γ Γ′ dΓ dΓ′ A f K reflection

  pulled-set : IsSet Form.PulledTotal
  pulled-set = Σ-set Γ′-set (λ γ′ → Output.family-set K (f γ′))

  module _
    (@♭ θ : ʃ d → Form.PulledTotal)
    (@♭ θ-η : (x : Σ Γ′ (A ∘ f)) → θ (η d x) ≡ function Form.pulled-unit x)
    where

    canonical : (w : ʃ d) → Form.comparison-total w ≡ θ w
    canonical = unique d Form.PulledTotal pulled-set Form.pulled-discrete
      Form.comparison-total θ
      (λ x → Output.factor-on-unit reflection Form.PulledTotal
               Form.pulled-discrete Form.pulled-projection
               Form.pulled-set-fibers Form.pulled-unit x
             ∙ sym (θ-η x))

    total : IsEquiv θ → Form.TotalComparisonIsEquivalence
    total E = quasi-inverse (inverse E)
      (λ v → canonical (inverse E v) ∙ section E v)
      (λ w → ap (inverse E) (canonical w) ∙ retraction E w)
