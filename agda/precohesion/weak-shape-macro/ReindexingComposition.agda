{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The canonical reindexing comparisons compose. Postulate-free.
-- Claude (Fable), 13 November 2026; fable-impl-10. FOUNDATION-COMPLETION-
-- GATES-01 gate G2 ("identity/composition/choice naturality: specify exact
-- laws"); used by ContextSpecialisation for field B9 of FABLE-REVIEW-05
-- section 4.
--
-- Fix discrete types and maps  Γ″ --g--> Γ′ --f--> Γ,  a family A over Γ,
-- and relative reflections K of A, K′ of A ∘ f, K″ of A ∘ f ∘ g. There are
-- three canonical comparisons (ShapeReindexing):
--
--   Outer   along f       fibres of K′ → fibres of K
--   Inner   along g       fibres of K″ → fibres of K′
--   Whole   along f ∘ g   fibres of K″ → fibres of K
--
--   Pasting.natural     Whole.comparison-total z ≡ pull (Inner.comparison-total z)
--                       where pull applies Outer.comparison in each fibre
--   Pasting.fibrewise   Whole.comparison γ″ w
--                         ≡ Outer.comparison (g γ″) (Inner.comparison γ″ w)
--
-- Both hold at every point, for discrete bases of any truncation level:
-- no base is assumed to be a set. Proof: the two sides of `natural` are
-- maps over Γ″ out of the total space of K″ that restrict to the same map
-- along its unit (the unit laws of the three comparisons), so they are
-- equal as maps over Γ″ by the uniqueness half of K″; `fibrewise` is that
-- equality read in a fibre, triangle included. Function extensionality at
-- the level of the data is a crisp hypothesis, as in ShapeChoice.
--
-- Consequences (ordinary evidence, never made crisp):
--   Pasting.compose-fibres   Outer and Inner invertible ⇒ Whole invertible
--   Pasting.cancel-fibres    Outer and Whole invertible ⇒ Inner invertible
--   Pasting.compose-total, cancel-total   the same with Inner and Whole
--                            in TOTAL form. The hypothesis on Outer stays
--                            in FIBRE form in these two as well; when Γ′
--                            is a set, ReindexingAssembly.FromTotal
--                            converts total evidence for Outer.
--
-- NOTHING HERE SAYS THAT ANY COMPARISON IS INVERTIBLE. In particular the
-- third two-out-of-three direction (Inner and Whole invertible ⇒ Outer
-- invertible) is not stated: it holds only at points in the image of g.
module ReindexingComposition where

open import Foundations
open import RelativeSliceShape
open import PullbackSetFibers using (transport)
import ShapeChoice
open ShapeChoice using (FunExtAt; compose-over)
open import Adjointify using (quasi-inverse)
open import ReindexingAssembly using (module TotalForm)

private
  -- A fibrewise map commutes with transport in the base.
  transport-natural : ∀ {a b c} {X : Set a} {P : X → Set b} {Q : X → Set c}
                    → (m : (x : X) → P x → Q x)
                    → {x y : X} (r : x ≡ y) (v : P x)
                    → transport Q r (m x v) ≡ m y (transport P r v)
  transport-natural m refl v = refl

module Pasting
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Γ Γ′ Γ″ : Set ℓ)
  (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′) (@♭ dΓ″ : Discrete Γ″)
  (@♭ A : Γ → Set ℓ) (@♭ f : Γ′ → Γ) (@♭ g : Γ″ → Γ′)
  (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ K′ : RelativeShapeOver Γ′ dΓ′ (A ∘ f))
  (@♭ K″ : RelativeShapeOver Γ″ dΓ″ (A ∘ f ∘ g)) where

  module Outer = TotalForm Γ Γ′ dΓ dΓ′ A f K K′
  module Inner = TotalForm Γ′ Γ″ dΓ′ dΓ″ (A ∘ f) g K′ K″
  module Whole = TotalForm Γ Γ″ dΓ dΓ″ A (f ∘ g) K K″

  private
    open ShapeChoice.Algebra fe using (compose-assoc)

    T″ : Set ℓ
    T″ = Output.Total K″

    unit″ : MapOver (fst {B = A ∘ f ∘ g}) (Output.projection K″)
    unit″ = over-map (Output.unit K″) (Output.unit-over K″)

  -- The comparison along f, applied in the fibres over Γ″.
  pull : Inner.PulledTotal → Whole.PulledTotal
  pull w = fst w , Outer.comparison (g (fst w)) (snd w)

  private
    pull-over : MapOver Inner.pulled-projection Whole.pulled-projection
    pull-over = over-map pull (λ _ → refl)

    composite : MapOver (Output.projection K″) Whole.pulled-projection
    composite = compose-over pull-over Inner.comparison-over

    pulled-units : compose-over pull-over Inner.pulled-unit ≡ Whole.pulled-unit
    pulled-units =
      ap (λ (G : (x : Σ Γ″ (A ∘ f ∘ g)) → Whole.PulledFamily (fst x))
            → over-map {q = Whole.pulled-projection}
                (λ x → fst x , G x) (λ _ → refl))
         (fe (λ x → Outer.comparison-on-unit (g (fst x)) (snd x)))

    composite-unit : compose-over composite unit″ ≡ Whole.pulled-unit
    composite-unit =
      compose-assoc pull-over Inner.comparison-over unit″
      ∙ ap (compose-over pull-over)
          (Output.factor-β K″ Inner.PulledTotal Inner.pulled-discrete
             Inner.pulled-projection Inner.pulled-set-fibers Inner.pulled-unit)
      ∙ pulled-units

    whole-unit : compose-over Whole.comparison-over unit″ ≡ Whole.pulled-unit
    whole-unit = Output.factor-β K″ Whole.PulledTotal Whole.pulled-discrete
      Whole.pulled-projection Whole.pulled-set-fibers Whole.pulled-unit

    -- Equal as maps over Γ″: functions and triangles.
    same : Whole.comparison-over ≡ composite
    same = ShapeChoice.Uniqueness.unique K″ Whole.PulledTotal
      Whole.pulled-discrete Whole.pulled-projection Whole.pulled-set-fibers
      Whole.comparison-over composite (whole-unit ∙ sym composite-unit)

  -- The pasting law for the total comparisons.
  natural : (z : Output.Total K″)
          → Whole.comparison-total z ≡ pull (Inner.comparison-total z)
  natural z = ap (λ m → function m z) same

  private
    -- The fibre map of a map over Γ″ into the pulled-back total space, in
    -- the form in which ShapeReindexing.comparison is defined.
    fibre-of : MapOver (Output.projection K″) Whole.pulled-projection
             → (γ″ : Γ″) → Output.family K″ γ″ → Whole.PulledFamily γ″
    fibre-of m γ″ w = transport Whole.PulledFamily
      (triangle m (fst w) ∙ snd w) (snd (function m (fst w)))

  -- The pasting law in the fibres.
  fibrewise : (γ″ : Γ″) (w : Output.family K″ γ″)
            → Whole.comparison γ″ w
              ≡ Outer.comparison (g γ″) (Inner.comparison γ″ w)
  fibrewise γ″ w =
    ap (λ m → fibre-of m γ″ w) same
    ∙ transport-natural {P = Inner.PulledFamily} {Q = Whole.PulledFamily}
        (λ x → Outer.comparison (g x))
        (triangle Inner.comparison-over (fst w) ∙ snd w)
        (snd (Inner.comparison-total (fst w)))

  ----------------------------------------------------------------------
  -- Invertibility along the pasting law. The evidence is ordinary.

  module _ (E : Outer.ComparisonIsEquivalence) where

    private
      unpull : Whole.PulledTotal → Inner.PulledTotal
      unpull w = fst w , inverse (E (g (fst w))) (snd w)

      pull-unpull : (w : Whole.PulledTotal) → pull (unpull w) ≡ w
      pull-unpull w = ap (λ (v : Whole.PulledFamily (fst w)) → fst w , v)
        (section (E (g (fst w))) (snd w))

      unpull-pull : (w : Inner.PulledTotal) → unpull (pull w) ≡ w
      unpull-pull w = ap (λ (v : Inner.PulledFamily (fst w)) → fst w , v)
        (retraction (E (g (fst w))) (snd w))

    -- Total forms.
    compose-total : Inner.TotalComparisonIsEquivalence
                  → Whole.TotalComparisonIsEquivalence
    compose-total I = quasi-inverse inv sec ret
      where
      inv : Whole.PulledTotal → T″
      inv w = inverse I (unpull w)

      sec : (w : Whole.PulledTotal) → Whole.comparison-total (inv w) ≡ w
      sec w = natural (inv w)
            ∙ ap pull (section I (unpull w))
            ∙ pull-unpull w

      ret : (z : T″) → inv (Whole.comparison-total z) ≡ z
      ret z = ap (λ u → inverse I (unpull u)) (natural z)
            ∙ ap (inverse I) (unpull-pull (Inner.comparison-total z))
            ∙ retraction I z

    cancel-total : Whole.TotalComparisonIsEquivalence
                 → Inner.TotalComparisonIsEquivalence
    cancel-total W = quasi-inverse inv sec ret
      where
      inv : Inner.PulledTotal → T″
      inv w = inverse W (pull w)

      sec : (w : Inner.PulledTotal) → Inner.comparison-total (inv w) ≡ w
      sec w = sym (unpull-pull (Inner.comparison-total (inv w)))
            ∙ ap unpull (sym (natural (inv w)) ∙ section W (pull w))
            ∙ unpull-pull w

      ret : (z : T″) → inv (Inner.comparison-total z) ≡ z
      ret z = ap (inverse W) (sym (natural z)) ∙ retraction W z

    -- Fibre forms.
    compose-fibres : Inner.ComparisonIsEquivalence
                   → Whole.ComparisonIsEquivalence
    compose-fibres I γ″ = quasi-inverse inv sec ret
      where
      inv : Whole.PulledFamily γ″ → Output.family K″ γ″
      inv y = inverse (I γ″) (inverse (E (g γ″)) y)

      sec : (y : Whole.PulledFamily γ″) → Whole.comparison γ″ (inv y) ≡ y
      sec y = fibrewise γ″ (inv y)
            ∙ ap (Outer.comparison (g γ″))
                 (section (I γ″) (inverse (E (g γ″)) y))
            ∙ section (E (g γ″)) y

      ret : (w : Output.family K″ γ″) → inv (Whole.comparison γ″ w) ≡ w
      ret w = ap inv (fibrewise γ″ w)
            ∙ ap (inverse (I γ″))
                 (retraction (E (g γ″)) (Inner.comparison γ″ w))
            ∙ retraction (I γ″) w

    cancel-fibres : Whole.ComparisonIsEquivalence
                  → Inner.ComparisonIsEquivalence
    cancel-fibres W γ″ = quasi-inverse inv sec ret
      where
      inv : Inner.PulledFamily γ″ → Output.family K″ γ″
      inv v = inverse (W γ″) (Outer.comparison (g γ″) v)

      sec : (v : Inner.PulledFamily γ″) → Inner.comparison γ″ (inv v) ≡ v
      sec v = sym (retraction (E (g γ″)) (Inner.comparison γ″ (inv v)))
            ∙ ap (inverse (E (g γ″)))
                 ( sym (fibrewise γ″ (inv v))
                 ∙ section (W γ″) (Outer.comparison (g γ″) v) )
            ∙ retraction (E (g γ″)) v

      ret : (w : Output.family K″ γ″) → inv (Inner.comparison γ″ w) ≡ w
      ret w = ap (inverse (W γ″)) (sym (fibrewise γ″ w))
            ∙ retraction (W γ″) w
