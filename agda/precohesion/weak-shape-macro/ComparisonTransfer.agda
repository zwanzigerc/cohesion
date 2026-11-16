{-# OPTIONS --cohesion --without-K --flat-split #-}

-- COMPARISON TRANSFER along the payload truncation, for ARBITRARY sources.
-- Opus, 14 November 2026; opus-shape0-main-01, implementing
-- OPUS-SHAPE0-COMPARISON-TRANSFER-RELEASE-01.txt, i.e.
-- SHAPE0-TRUNCATE-EXISTING-PAYLOAD-01 section 4 (FABLE-SET-PROOF-
-- ASSESSMENT-01 section 3; FABLE-IMPL-22 sections 2.5, 5.2), on frozen M22.
--
-- Telescope: exactly TruncatedPayloadExamples.SameComparisonType — crisp
-- ℓ, a crisp SetTruncation τ, crisp FunExtAt ℓ, crisp discrete bases B B′
-- (no sethood used), crisp A : B → Set ℓ with ARBITRARY fibres, crisp
-- f : B′ → B, and two crisp payload VARIABLES
--     K : RelativeShapeOver B dB A,   K′ : RelativeShapeOver B′ dB′ (A ∘ f).
-- With K₀ = truncate-payload K and K′₀ = truncate-payload K′ (TruncatedPayload),
-- C = Comparison … K K′ and C₀ = Comparison … K₀ K′₀ (ShapeReindexing):
--
--   comparisons-agree : ComparisonsAgree
--                       (= C₀.comparison-over ≡ C.comparison-over,
--                        M22's own source-checked statement type)
--   transfer          : Transfer
--                       (= C₀.ComparisonIsEquivalence
--                          → C.ComparisonIsEquivalence, M22's type)
--
-- The proof (all whole MapOver paths, all structural data crisp). With
-- pre′ the precomposition with the unit of K′ (ShapeChoice.Uniqueness),
-- R′ the restriction along ∣_∣₀ (TruncatedPayload.Over.restrict for K′),
-- and the test target (C.PulledTotal, C.pulled-discrete,
-- C.pulled-projection, C.pulled-set-fibers):
--   step₁  pre′ C₀.comparison-over ≡ R′ (pre′₀ C₀.comparison-over)
--          — sym of Truncate.OnPayload.Test.square for K′ at that target;
--   step₂  ≡ R′ C₀.pulled-unit
--          — ap R′ of Output.factor-β for K′₀, with C₀'s OWN discrete and
--            set-fibre evidence (the evidence inside C₀.comparison-over);
--   step₃  ≡ C.pulled-unit
--          — fibrewise unit-β for K at (f b′, a), under the outer pair
--            (b′ , _) with outer triangle refl; whole path by
--            Truncate.Over.uncurry and two uses of fe;
--   step₄  ≡ pre′ C.comparison-over
--          — sym of the old Output.factor-β for K′, with C's evidence.
-- ShapeChoice.Uniqueness.unique for K′ turns the crisp whole path
-- pre-agree = step₁ ∙ step₂ ∙ step₃ ∙ step₄ into comparisons-agree.
-- No equality of evidence or of payload records is proved or needed: the
-- new and old pullback targets and projections are convertible by M22's
-- construction, even for variable K, K′.
--
-- Transfer. fibre-map M γ′ is ShapeReindexing's fibre formula applied to an
-- arbitrary MapOver record M, transport along its TRIANGLE path included;
-- C.comparison and C₀.comparison are fibre-map of the respective actual
-- comparison-over records by conversion (fibre-map-actual,
-- fibre-map-actual₀ are refl). comparison-fibres-agree is ap of
-- comparisons-agree, and transfer transports the ORDINARY input witness
-- along comparisons-agree.
--
-- Used: TruncatedPayload (Truncate.Over.restrict / uncurry,
-- Truncate.OnPayload.Test.square, Truncate.unit-β), ShapeReindexing
-- (Comparison), ShapeChoice (Uniqueness.unique), RelativeSliceShape
-- (Output.factor-β), PullbackSetFibers.transport. NOT used: any
-- continuity, Nullstellensatz or product witness, propositional
-- extensionality, cross-level FE, sethood of B or B′, dependent
-- elimination from τ₀, a payload match, a new shape or declaration.
-- Nothing is postulated. Not --safe (--flat-split is infective from the
-- imported foundation).
module ComparisonTransfer where

open import Foundations
open import RelativeSliceShape
open import PullbackSetFibers using (transport)
open import ShapeChoice using (FunExtAt; module Uniqueness)
open import OrdinaryTruncation using (SetTruncation)
open import TruncatedPayload using (module Truncate)
open import TruncatedPayloadExamples using (module SameComparisonType)

module Proof {@♭ ℓ : Level} (@♭ τ : SetTruncation ℓ)
  (@♭ fe : FunExtAt ℓ)
  (@♭ B B′ : Set ℓ) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ A : B → Set ℓ) (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f)) where

  -- M22's statement types and the two actual comparisons C, C₀.
  open SameComparisonType τ fe B B′ dB dB′ A f K K′ public

  open SetTruncation τ using (∣_∣₀)

  private
    module T = Truncate τ fe {B} {dB} {A}
    module T′ = Truncate τ fe {B′} {dB′} {A ∘ f}

  K₀ : RelativeShapeOver B dB T.A₀
  K₀ = T.truncate-payload K

  K′₀ : RelativeShapeOver B′ dB′ T′.A₀
  K′₀ = T′.truncate-payload K′

  ----------------------------------------------------------------------
  -- Crisp part: everything below is built from the crisp parameters only.

  -- The common test target: the old pullback with its evidence.
  module U = Uniqueness K′ C.PulledTotal C.pulled-discrete
    C.pulled-projection C.pulled-set-fibers
  module R′ = T′.Over C.PulledTotal C.pulled-projection C.pulled-set-fibers
  module Sq = T′.OnPayload.Test K′ C.PulledTotal C.pulled-discrete
    C.pulled-projection C.pulled-set-fibers

  -- step₁: the square of TruncatedPayload, read backwards.
  step₁ : U.pre C₀.comparison-over ≡ R′.restrict (Sq.pre₀ C₀.comparison-over)
  step₁ = sym (Sq.square C₀.comparison-over)

  -- step₂: R′ applied to the NEW factor-β (C₀'s own evidence).
  new-factor-β : Sq.pre₀ C₀.comparison-over ≡ C₀.pulled-unit
  new-factor-β = Output.factor-β K′₀ C₀.PulledTotal C₀.pulled-discrete
    C₀.pulled-projection C₀.pulled-set-fibers C₀.pulled-unit

  step₂ : R′.restrict (Sq.pre₀ C₀.comparison-over) ≡ R′.restrict C₀.pulled-unit
  step₂ = ap R′.restrict new-factor-β

  -- step₃: the restricted new pulled unit is the old pulled unit, by
  -- unit-β for K over f b′, inside the outer pair with triangle refl.
  pulled-unit-fibre : (b′ : B′) (a : A (f b′))
    → _≡_ {A = Fiber C.pulled-projection b′}
        ((b′ , Output.family-unit K₀ (f b′) ∣ a ∣₀) , refl)
        ((b′ , Output.family-unit K (f b′) a) , refl)
  pulled-unit-fibre b′ a =
    ap (λ u → (b′ , u) , refl) (T.unit-β K (f b′) a)

  step₃ : R′.restrict C₀.pulled-unit ≡ C.pulled-unit
  step₃ = ap (R′.uncurry {F = A ∘ f})
    (fe (λ b′ → fe (λ a → pulled-unit-fibre b′ a)))

  -- step₄: the OLD factor-β (C's own evidence), backwards.
  old-factor-β : U.pre C.comparison-over ≡ C.pulled-unit
  old-factor-β = Output.factor-β K′ C.PulledTotal C.pulled-discrete
    C.pulled-projection C.pulled-set-fibers C.pulled-unit

  step₄ : C.pulled-unit ≡ U.pre C.comparison-over
  step₄ = sym old-factor-β

  -- The two comparisons agree after precomposition with the unit of K′.
  pre-agree : U.pre C₀.comparison-over ≡ U.pre C.comparison-over
  pre-agree = step₁ ∙ step₂ ∙ step₃ ∙ step₄

  -- THE EQUALITY OF THE TWO ACTUAL MapOver COMPARISONS.
  comparisons-agree : ComparisonsAgree
  comparisons-agree =
    U.unique C₀.comparison-over C.comparison-over pre-agree

  ----------------------------------------------------------------------
  -- The fibre formula of ShapeReindexing, for an arbitrary record M.

  fibre-map : MapOver (Output.projection K′) C.pulled-projection
            → (γ′ : B′) → Output.family K′ γ′ → C.PulledFamily γ′
  fibre-map M γ′ w =
    transport C.PulledFamily (triangle M (fst w) ∙ snd w)
      (snd (function M (fst w)))

  fibre-map-actual : (γ′ : B′) (w : Output.family K′ γ′)
                   → fibre-map C.comparison-over γ′ w ≡ C.comparison γ′ w
  fibre-map-actual γ′ w = refl

  fibre-map-actual₀ : (γ′ : B′) (w : Output.family K′₀ γ′)
                    → fibre-map C₀.comparison-over γ′ w ≡ C₀.comparison γ′ w
  fibre-map-actual₀ γ′ w = refl

  comparison-fibres-agree : (γ′ : B′) → C₀.comparison γ′ ≡ C.comparison γ′
  comparison-fibres-agree γ′ = ap (λ M → fibre-map M γ′) comparisons-agree

  ----------------------------------------------------------------------
  -- Ordinary part: the input equivalence witness is an ordinary argument.

  transfer : Transfer
  transfer w =
    transport (λ M → (γ′ : B′) → IsEquiv (fibre-map M γ′)) comparisons-agree w
