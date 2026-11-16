{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Over discrete bases with decidable equality the canonical reindexing
-- comparison is an equivalence. Postulate-free. Claude (Fable), 13 November
-- 2026; fable-impl-10. HANDOFF-18 correction 2 and M8-REINDEXING-ASSEMBLY-
-- SOURCE-AUDIT-01 section 6, where this argument is given in prose for one
-- closed diagram; GENERIC-MAIN-SCHEMA-ADEQUACY-01 section 6, last paragraph.
--
-- Let Γ, Γ′ be discrete with decidable equality, f : Γ′ → Γ, A a family
-- over Γ, K a relative reflection of A and K′ one of A ∘ f. Then
--
--   Stable.fibres : ComparisonIsEquivalence
--   Stable.total  : TotalComparisonIsEquivalence
--
-- for the canonical comparison of ShapeReindexing, from function
-- extensionality at the level of the data and nothing else: no product
-- law, no Nullstellensatz, no continuity.
--
-- Proof. At a crisp point γ′ both fibres are terminal reflections of the
-- one type A (f γ′) (DecidableBase.Fibre, used once for K′ at γ′ and once
-- for K at f γ′). The comparison preserves the units, so it has the
-- canonical comparison of the two reflections as a two-sided inverse, by
-- uniqueness on each side (UnitPreserving, a general fact about two
-- terminal reflections of one type). Every point of the discrete Γ′ is
-- reached from crisp points (discrete-ind).
--
-- Consequences for what a test can show.
--  * A diagram whose two bases have decidable equality cannot exhibit a
--    comparison that fails to be invertible: there the conclusion of the
--    local-connectedness theorem is a theorem of the weak core with
--    extensionality. The closed Bool diagram of ReindexingAcceptanceA is
--    such a diagram (module Derived there).
--  * Discrete SETS for which no decision procedure is available, and
--    discrete bases that are not sets, are OUTSIDE this theorem. Nothing
--    is proved about them here, and no continuity theorem for them is
--    established anywhere in this tree. The main target concerns
--    discrete set bases.
--  * Fibre.fibre-data is the place where decidability enters: it extends a
--    map on one fibre by a constant elsewhere. This module does not
--    promote a captured fibre to a terminal reflection in any other case.
module DecidableReindexing where

open import Foundations
open import RelativeSliceShape
open import ShapeChoice using (FunExtAt)
open import DiscretePullback using (discrete-ind)
open import GlobalPrecohesion
open import GlobalChoice using (set-equiv; module Across)
open import DecidableBase using (DecEq; module Fibre)
open import ReindexingAssembly using (module TotalForm)

-- A map between two terminal reflections of one type that preserves the
-- units is the canonical comparison of the two, hence an equivalence.
-- Stated for abstract shape data: with the data of DecidableBase.Fibre
-- written out, the same three uses of uniqueness take twenty times as long
-- to check.
module UnitPreserving
  {@♭ ℓ : Level} {@♭ X : Set ℓ} (@♭ s t : ShapeData X)
  (@♭ h : ʃ s → ʃ t) (@♭ h-η : (x : X) → h (η s x) ≡ η t x) where

  private
    module There = Across s t
    module Back = Across t s

  canonical : (w : ʃ s) → h w ≡ There.across w
  canonical = unique s (ʃ t) (ʃ-set t) (ʃ-discrete t) h There.across
    (λ x → h-η x ∙ sym (There.across-η x))

  private
    sec : (y : ʃ t) → h (Back.across y) ≡ y
    sec = unique t (ʃ t) (ʃ-set t) (ʃ-discrete t)
      (λ y → h (Back.across y)) (λ y → y)
      (λ x → ap h (Back.across-η x) ∙ h-η x)

    ret : (w : ʃ s) → Back.across (h w) ≡ w
    ret = unique s (ʃ s) (ʃ-set s) (ʃ-discrete s)
      (λ w → Back.across (h w)) (λ w → w)
      (λ x → ap Back.across (h-η x) ∙ Back.across-η x)

  equivalence : IsEquiv h
  equivalence = set-equiv (ʃ-set t) Back.across sec ret

module Stable
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Γ Γ′ : Set ℓ)
  (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
  (@♭ dec : DecEq Γ) (@♭ dec′ : DecEq Γ′)
  (@♭ A : Γ → Set ℓ) (@♭ f : Γ′ → Γ)
  (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ K′ : RelativeShapeOver Γ′ dΓ′ (A ∘ f)) where

  open TotalForm Γ Γ′ dΓ dΓ′ A f K K′

  module AtCrisp (@♭ γ′ : Γ′) where

    -- The fibre of K′ at γ′ and the fibre of K at f γ′: two terminal
    -- reflections of A (f γ′), with the units of K′ and of K.
    source : ShapeData (A (f γ′))
    source = Fibre.fibre-data fe dec′ K′ γ′

    target : ShapeData (A (f γ′))
    target = Fibre.fibre-data fe dec K (f γ′)

    private
      module U = UnitPreserving source target
        (comparison γ′) (comparison-on-unit γ′)

    -- The comparison is the canonical map between the two reflections.
    canonical : (w : ʃ source) → comparison γ′ w ≡ Across.across source target w
    canonical = U.canonical

    equivalence : IsEquiv (comparison γ′)
    equivalence = U.equivalence

  -- Every point of a discrete type is reached from the crisp ones.
  fibres : ComparisonIsEquivalence
  fibres = discrete-ind dΓ′ (λ γ′ → IsEquiv (comparison γ′))
    (λ γ′ → AtCrisp.equivalence γ′)

  total : TotalComparisonIsEquivalence
  total = FromFibres.total fibres
