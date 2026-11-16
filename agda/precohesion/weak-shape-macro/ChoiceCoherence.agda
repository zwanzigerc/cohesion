{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The two ways of comparing choices agree. Postulate-free. Claude (Fable),
-- 13 November 2026; fable-impl-07; HANDOFF-06 item 6 ("choice coherence"),
-- FABLE-REVIEW-03 section 8.2, FABLE03-SECTION8-PLAN-REVIEW-01 section 4.
--
-- Over a discrete SET Γ there are two notions of a choice of shape for a
-- family A, and each has its canonical comparison of two choices:
--   relative reflections K, L over Γ      ShapeChoice.Choice.forward
--   terminal shape data s, t of Σ Γ A     GlobalChoice.Across.across
-- TotalBridge and TotalConverse pass between the two notions without
-- changing carriers or units. This module shows that they also carry one
-- comparison to the other, pointwise:
--
--   Relative.coherent    for relative K, L: the relative comparison is the
--                        terminal comparison of their total data. Needs no
--                        converse (TotalBridge only).
--   Relative.over        hence the terminal comparison lies over Γ.
--   Terminal.coherent    for terminal s, t: the terminal comparison is the
--                        relative comparison of their converses.
--   Terminal.over        the terminal comparison commutes with the two
--                        projections to Γ that the converse defines.
--   Fibrewise.coherent   over a base with decidable equality, at a crisp
--                        point: the fibre of the relative comparison is the
--                        terminal comparison of the two fibre data.
--
-- Every statement is an equality of values at each point, proved by the
-- uniqueness half of the SOURCE data; none is an equality of maps, of
-- records or of types. Function extensionality occurs only as the crisp
-- hypothesis that the bridges and ShapeChoice already have.
module ChoiceCoherence where

open import Foundations
import RelativeSliceShape as R
open R using (RelativeShapeOver; function; triangle)
import ShapeChoice
open ShapeChoice using (FunExtAt)
import GlobalChoice
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; unique)
open import TotalBridge using (module TotalData)
open import TotalConverse using (module Converse)
open import DecidableBase using (DecEq; decidable-set; module Fibre)

module _ {@♭ ℓ : Level} where

  module Relative
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
    {@♭ A : Γ → Set ℓ} (@♭ K L : RelativeShapeOver Γ dΓ A) where

    sK : ShapeData (Σ Γ A)
    sK = TotalData.total-data fe Γ-set K

    sL : ShapeData (Σ Γ A)
    sL = TotalData.total-data fe Γ-set L

    private
      module Rel = ShapeChoice.Choice fe K L
      module Ter = GlobalChoice.Across sK sL

    coherent : (z : R.Output.Total K) → Rel.forward z ≡ Ter.across z
    coherent = unique sK (ʃ sL) (ʃ-set sL) (ʃ-discrete sL)
      Rel.forward Ter.across
      (λ a → Rel.forward-on-unit a ∙ sym (Ter.across-η a))

    over : (z : R.Output.Total K)
         → R.Output.projection L (Ter.across z) ≡ R.Output.projection K z
    over z = ap (R.Output.projection L) (sym (coherent z))
           ∙ triangle Rel.forward-over z

  module Terminal
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
    {@♭ A : Γ → Set ℓ} (@♭ s t : ShapeData (Σ Γ A)) where

    Ks : RelativeShapeOver Γ dΓ A
    Ks = Converse.relative fe {dΓ = dΓ} Γ-set s

    Kt : RelativeShapeOver Γ dΓ A
    Kt = Converse.relative fe {dΓ = dΓ} Γ-set t

    private
      module Rel = ShapeChoice.Choice fe Ks Kt
      module Ter = GlobalChoice.Across s t

    coherent : (z : ʃ s) → Rel.forward z ≡ Ter.across z
    coherent = unique s (ʃ t) (ʃ-set t) (ʃ-discrete t)
      Rel.forward Ter.across
      (λ a → Rel.forward-on-unit a ∙ sym (Ter.across-η a))

    over : (z : ʃ s)
         → R.Output.projection Kt (Ter.across z) ≡ R.Output.projection Ks z
    over z = ap (R.Output.projection Kt) (sym (coherent z))
           ∙ triangle Rel.forward-over z

  module Fibrewise
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ dec : DecEq Γ)
    {@♭ A : Γ → Set ℓ} (@♭ K L : RelativeShapeOver Γ dΓ A)
    (@♭ γ₀ : Γ) where

    dK : ShapeData (A γ₀)
    dK = Fibre.fibre-data fe dec K γ₀

    dL : ShapeData (A γ₀)
    dL = Fibre.fibre-data fe dec L γ₀

    private
      module Rel = ShapeChoice.FiberChoice fe K L
      module Ter = GlobalChoice.Across dK dL

    coherent : (w : ʃ dK) → Rel.forward γ₀ w ≡ Ter.across w
    coherent = unique dK (ʃ dL) (ʃ-set dL) (ʃ-discrete dL)
      (Rel.forward γ₀) Ter.across
      (λ a → Rel.forward-on-unit γ₀ a ∙ sym (Ter.across-η a))
