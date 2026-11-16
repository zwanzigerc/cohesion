{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The conclusion of the reindexing theorem does not depend on the choice
-- of the two reflections. Postulate-free. Claude (Fable), 13 November
-- 2026; fable-impl-08; FABLE-REVIEW-05 section 4 (field A8),
-- REFLECTION-ISSUES R19 and R31.
--
-- Fix a family A over a discrete Γ and a map f : Γ′ → Γ of discrete types.
-- Let K, L be two relative reflections of A over Γ, and K′, L′ two of
-- A ∘ f over Γ′: for instance one pair made from closed total shapes by
-- TotalConverse and one pair of captures or closed slice declarations.
-- Each pair has its canonical comparison (ShapeReindexing). Then
--
--   natural      the square of the two total comparisons with the canonical
--                comparisons of the choices (ShapeChoice) commutes, at
--                every point. By the uniqueness half of K′.
--   Transfer.total   if the total comparison of (K, K′) is an equivalence,
--                    so is the one of (L, L′).
--   fibre-form   the same for the fibre form, over a set Γ′.
--
-- So a theorem proved for the payloads that an assembly layer selects holds
-- for every other choice of payloads of the same diagram, and is about the
-- canonical comparison of each. Function extensionality at the level of
-- the data is a crisp hypothesis, as in ShapeChoice. Nothing here says
-- that any comparison is an equivalence.
module ReindexingChoice where

open import Foundations
open import RelativeSliceShape
import ShapeChoice
open ShapeChoice using (FunExtAt; compose-over)
open import Adjointify using (quasi-inverse)
open import ReindexingAssembly using (module TotalForm)

module Independence
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  (@♭ Γ Γ′ : Set ℓ)
  (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
  (@♭ A : Γ → Set ℓ) (@♭ f : Γ′ → Γ)
  (@♭ K L : RelativeShapeOver Γ dΓ A)
  (@♭ K′ L′ : RelativeShapeOver Γ′ dΓ′ (A ∘ f)) where

  -- The four instances the statements below are about. Public since
  -- fable-impl-11, so that a client can name the modules that occur in
  -- the type of `natural` instead of instantiating them a second time:
  --   TK  the comparison of the pair (K, K′)      TL  that of (L, L′)
  --   C′  the canonical comparison K′ → L′ on total spaces (over Γ′)
  --   FC  the canonical comparison K → L, fibrewise (over Γ)
  module TK = TotalForm Γ Γ′ dΓ dΓ′ A f K K′
  module TL = TotalForm Γ Γ′ dΓ dΓ′ A f L L′
  module C′ = ShapeChoice.Choice fe K′ L′
  module FC = ShapeChoice.FiberChoice fe K L

  open ShapeChoice.Algebra fe using (compose-assoc)

  -- The comparison of the two pulled-back reflections, fibrewise over Γ′.
  pull : TK.PulledTotal → TL.PulledTotal
  pull w = fst w , FC.forward (f (fst w)) (snd w)

  private
    pull-over : MapOver TK.pulled-projection TL.pulled-projection
    pull-over = over-map pull (λ _ → refl)

    g : MapOver (Output.projection K′) TL.pulled-projection
    g = compose-over TL.comparison-over C′.forward-over

    h : MapOver (Output.projection K′) TL.pulled-projection
    h = compose-over pull-over TK.comparison-over

    -- Both composites restrict, along the unit of K′, to the pulled-back
    -- unit of L.
    g-unit : compose-over g C′.unit-s ≡ TL.pulled-unit
    g-unit =
      compose-assoc TL.comparison-over C′.forward-over C′.unit-s
      ∙ ap (compose-over TL.comparison-over) C′.forward-unit
      ∙ Output.factor-β L′ TL.PulledTotal TL.pulled-discrete
          TL.pulled-projection TL.pulled-set-fibers TL.pulled-unit

    pulled-units : compose-over pull-over TK.pulled-unit ≡ TL.pulled-unit
    pulled-units =
      ap (λ (G : (x : Σ Γ′ (A ∘ f)) → TL.PulledFamily (fst x))
            → over-map {q = TL.pulled-projection}
                (λ x → fst x , G x) (λ _ → refl))
         (fe (λ x → FC.forward-on-unit (f (fst x)) (snd x)))

    h-unit : compose-over h C′.unit-s ≡ TL.pulled-unit
    h-unit =
      compose-assoc pull-over TK.comparison-over C′.unit-s
      ∙ ap (compose-over pull-over)
          (Output.factor-β K′ TK.PulledTotal TK.pulled-discrete
             TK.pulled-projection TK.pulled-set-fibers TK.pulled-unit)
      ∙ pulled-units

    same : g ≡ h
    same = ShapeChoice.Uniqueness.unique K′ TL.PulledTotal TL.pulled-discrete
      TL.pulled-projection TL.pulled-set-fibers g h (g-unit ∙ sym h-unit)

  -- The square commutes at every point of the total space of K′.
  natural : (z : Output.Total K′)
          → TL.comparison-total (C′.forward z) ≡ pull (TK.comparison-total z)
  natural z = ap (λ m → function m z) same

  private
    unpull : TL.PulledTotal → TK.PulledTotal
    unpull w = fst w , FC.backward (f (fst w)) (snd w)

    pull-unpull : (w : TL.PulledTotal) → pull (unpull w) ≡ w
    pull-unpull w = ap (λ (v : TL.PulledFamily (fst w)) → fst w , v)
      (FC.forward-backward (f (fst w)) (snd w))

    unpull-pull : (w : TK.PulledTotal) → unpull (pull w) ≡ w
    unpull-pull w = ap (λ (v : TK.PulledFamily (fst w)) → fst w , v)
      (FC.backward-forward (f (fst w)) (snd w))

  -- Total form: from the pair (K, K′) to the pair (L, L′).
  module Transfer (E : TK.TotalComparisonIsEquivalence) where

    private
      inv : TL.PulledTotal → Output.Total L′
      inv w = C′.forward (inverse E (unpull w))

      sec : (w : TL.PulledTotal) → TL.comparison-total (inv w) ≡ w
      sec w = natural (inverse E (unpull w))
            ∙ ap pull (section E (unpull w))
            ∙ pull-unpull w

      ret : (z′ : Output.Total L′) → inv (TL.comparison-total z′) ≡ z′
      ret z′ =
        ap (λ u → C′.forward (inverse E (unpull (TL.comparison-total u))))
           (sym (C′.forward-backward z′))
        ∙ ap (λ u → C′.forward (inverse E (unpull u)))
             (natural (C′.backward z′))
        ∙ ap (λ u → C′.forward (inverse E u))
             (unpull-pull (TK.comparison-total (C′.backward z′)))
        ∙ ap C′.forward (retraction E (C′.backward z′))
        ∙ C′.forward-backward z′

    total : TL.TotalComparisonIsEquivalence
    total = quasi-inverse inv sec ret

  -- Fibre form, over a set.
  fibre-form : IsSet Γ′ → TK.ComparisonIsEquivalence
             → TL.ComparisonIsEquivalence
  fibre-form Γ′-set E =
    TL.FromTotal.fibres Γ′-set (Transfer.total (TK.FromFibres.total E))
