{-# OPTIONS --cohesion --without-K --flat-split #-}

-- External products over discrete sets: the relative reflection of an
-- external product and its base square; and, where the bases have decidable
-- equality, the product law for the fibres at every pair of crisp points
-- from the closed product axiom for the two total spaces. Postulate-free.
-- Claude (Fable), 13 November 2026; fable-impl-07; HANDOFF-06 item 6,
-- FABLE-REVIEW-03 sections 8.3 and 8.4, FABLE03-SECTION8-PLAN-REVIEW-01
-- sections 5 and 6.
--
-- fable-impl-09 (HANDOFF-17 section 1): the module External now asks only
-- that Γ₁ and Γ₂ are SETS. Decidable equality is a parameter of AtPoint
-- alone, where a fibre of a reflection is promoted to terminal shape data.
-- No definition of the proofs changed.
--
-- Data, all crisp, at one level ℓ: discrete SETS Γ₁, Γ₂; families A₁ over
-- Γ₁ and A₂ over Γ₂; terminal
-- shape data s₁, s₂, s₁₂ of the total spaces
--     X₁ = Σ Γ₁ A₁,   X₂ = Σ Γ₂ A₂   and of   X₁ × X₂;
-- and function extensionality at ℓ. The external product is the family
--     External (γ₁ , γ₂) = A₁ γ₁ × A₂ γ₂     over Γ₁ × Γ₂.
--
--   s-ext        terminal shape data of Σ (Γ₁ × Γ₂) External, with the
--                carrier of s₁₂: transfer along the rearrangement of pairs.
--   K₁, K₂, K₁₂  the relative reflections over Γ₁, Γ₂ and Γ₁ × Γ₂
--                (TotalConverse), with the carriers and units of the data.
--   square       the canonical comparison  ʃ s₁₂ → ʃ s₁ × ʃ s₂  lies over
--                Γ₁ × Γ₂. Proved by uniqueness into the discrete set
--                Γ₁ × Γ₂. No product axiom is used for this.
--   AtPoint dec₁ dec₂ γ₁ γ₂      (decidable equality of Γ₁ and Γ₂ enters here)
--     d₁, d₂, d₁₂     terminal shape data of A₁ γ₁, A₂ γ₂ and A₁ γ₁ × A₂ γ₂:
--                     the fibres of K₁, K₂, K₁₂ (DecidableBase.Fibre).
--     canonical       the canonical comparison of d₁, d₂, d₁₂ is the map
--                     that `square` induces on fibres. By uniqueness.
--     fibre-product   PreservesProduct s₁ s₂ s₁₂ → PreservesProduct d₁ d₂ d₁₂.
--     product-for     the same conclusion for ANY terminal shape data
--                     t₁, t₂, t₁₂ of the three types, for instance the data
--                     of fresh captures at the current point of an open
--                     context (GlobalChoice.ProductChoice).
--
-- The product hypothesis is ORDINARY. The conclusions are terms in that
-- hypothesis and in crisp data, so they can be used crisply exactly when
-- the hypothesis can; a closed declared product axiom can
-- (ExternalProductExamples; the negative probe ExternalProductOrdinary).
--
-- A practical note. d₁, d₂, d₁₂ unfold to large terms. A client that
-- writes the type  PreservesProduct d₁ d₂ d₁₂  through a module instance
-- makes Agda compare two spellings of that type by unfolding both, which
-- exhausted a 3 GB heap in the first version of the example. Use
-- product-for from outside this module.
--
-- What is NOT here. External asks for set bases and AtPoint for decidable
-- equality; in particular neither applies to a context containing a type
-- variable. No statement that the relative reflection of a family
-- restricted along a map is the restriction of the reflection: the points
-- γ₁, γ₂ are crisp, and a crisp point of a decidable set is a complemented
-- subobject. The shared-context case is the case γ₁ = γ₂ of this module,
-- read at a crisp point; it is not a pullback along the diagonal.
module ExternalProduct where

open import Foundations
import RelativeSliceShape as R
open R using (RelativeShapeOver)
open import FlatContext using (fiber-path)
open import ShapeChoice using (FunExtAt)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalPrecohesion
open import GlobalChoice using (set-equiv; ×-set; module Along; module ProductChoice)
open import DecidableBase using (Dec; yes; no; DecEq; decidable-set; module Fibre)
open import TotalConverse using (module Converse)

------------------------------------------------------------------------
-- Decidable equality of a product.

×-dec : ∀ {a b} {A : Set a} {B : Set b} → DecEq A → DecEq B → DecEq (A × B)
×-dec dA dB (x , y) (x′ , y′) = both (dA x x′) (dB y y′)
  where
  both : Dec (x ≡ x′) → Dec (y ≡ y′) → Dec ((x , y) ≡ (x′ , y′))
  both (yes p) (yes q) = yes (pair-path p q)
  both (yes _) (no n) = no (λ e → n (ap snd e))
  both (no n) _ = no (λ e → n (ap fst e))

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------
  -- The rearrangement of pairs. Both laws hold by the eta rule of Σ.

  module Shuffle {Γ₁ Γ₂ : Set ℓ} (A₁ : Γ₁ → Set ℓ) (A₂ : Γ₂ → Set ℓ) where

    External : Γ₁ × Γ₂ → Set ℓ
    External γ = A₁ (fst γ) × A₂ (snd γ)

    together : Σ Γ₁ A₁ × Σ Γ₂ A₂ → Σ (Γ₁ × Γ₂) External
    together w = (fst (fst w) , fst (snd w)) , (snd (fst w) , snd (snd w))

    apart : Σ (Γ₁ × Γ₂) External → Σ Γ₁ A₁ × Σ Γ₂ A₂
    apart z = (fst (fst z) , fst (snd z)) , (snd (fst z) , snd (snd z))

    together-apart : (z : Σ (Γ₁ × Γ₂) External) → together (apart z) ≡ z
    together-apart z = refl

    apart-together : (w : Σ Γ₁ A₁ × Σ Γ₂ A₂) → apart (together w) ≡ w
    apart-together w = refl

  ----------------------------------------------------------------------

  module External
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ₁ Γ₂ : Set ℓ}
    {@♭ dΓ₁ : Discrete Γ₁} {@♭ dΓ₂ : Discrete Γ₂}
    (@♭ Γ₁-set : IsSet Γ₁) (@♭ Γ₂-set : IsSet Γ₂)
    {@♭ A₁ : Γ₁ → Set ℓ} {@♭ A₂ : Γ₂ → Set ℓ}
    (@♭ s₁ : ShapeData (Σ Γ₁ A₁)) (@♭ s₂ : ShapeData (Σ Γ₂ A₂))
    (@♭ s₁₂ : ShapeData (Σ Γ₁ A₁ × Σ Γ₂ A₂)) where

    open Shuffle A₁ A₂ public

    base-discrete : Discrete (Γ₁ × Γ₂)
    base-discrete = SigmaDiscrete.discrete dΓ₁ (λ _ → dΓ₂)

    base-set : IsSet (Γ₁ × Γ₂)
    base-set = ×-set Γ₁-set Γ₂-set

    -- Shape data of the total space of the external product. Its carrier is
    -- the carrier of s₁₂ and its unit is the unit of s₁₂ after `apart`.
    s-ext : ShapeData (Σ (Γ₁ × Γ₂) External)
    s-ext = Along.along together apart together-apart apart-together s₁₂

    K₁ : RelativeShapeOver Γ₁ dΓ₁ A₁
    K₁ = Converse.relative fe {dΓ = dΓ₁} Γ₁-set s₁

    K₂ : RelativeShapeOver Γ₂ dΓ₂ A₂
    K₂ = Converse.relative fe {dΓ = dΓ₂} Γ₂-set s₂

    K₁₂ : RelativeShapeOver (Γ₁ × Γ₂) base-discrete External
    K₁₂ = Converse.relative fe {dΓ = base-discrete} base-set s-ext

    p₁ : ʃ s₁ → Γ₁
    p₁ = R.Output.projection K₁

    p₂ : ʃ s₂ → Γ₂
    p₂ = R.Output.projection K₂

    p₁₂ : ʃ s₁₂ → Γ₁ × Γ₂
    p₁₂ = R.Output.projection K₁₂

    private
      F₁ : ʃ s₁₂ → ʃ s₁
      F₁ = first s₁ s₂ s₁₂

      F₂ : ʃ s₁₂ → ʃ s₂
      F₂ = second s₁ s₂ s₁₂

      F₁-η : (x : Σ Γ₁ A₁ × Σ Γ₂ A₂) → F₁ (η s₁₂ x) ≡ η s₁ (fst x)
      F₁-η = rec-η s₁₂ (ʃ s₁) (ʃ-set s₁) (ʃ-discrete s₁) (λ q → η s₁ (fst q))

      F₂-η : (x : Σ Γ₁ A₁ × Σ Γ₂ A₂) → F₂ (η s₁₂ x) ≡ η s₂ (snd x)
      F₂-η = rec-η s₁₂ (ʃ s₂) (ʃ-set s₂) (ʃ-discrete s₂) (λ q → η s₂ (snd q))

    -- The canonical comparison of the three total shapes lies over the
    -- base: the projection of the external product is the pair of the
    -- projections of the factors. Uniqueness for s₁₂ at the target Γ₁ × Γ₂.
    square : (z : ʃ s₁₂) → p₁₂ z ≡ (p₁ (F₁ z) , p₂ (F₂ z))
    square = unique s₁₂ (Γ₁ × Γ₂) base-set base-discrete
      p₁₂ (λ z → p₁ (F₁ z) , p₂ (F₂ z))
      (λ x → R.Output.unit-over K₁₂ (together x)
           ∙ sym (pair-path
               (ap p₁ (F₁-η x) ∙ R.Output.unit-over K₁ (fst x))
               (ap p₂ (F₂-η x) ∙ R.Output.unit-over K₂ (snd x))))

    --------------------------------------------------------------------
    -- At a pair of crisp points, for bases with decidable equality.

    module AtPoint
      (@♭ dec₁ : DecEq Γ₁) (@♭ dec₂ : DecEq Γ₂)
      (@♭ γ₁ : Γ₁) (@♭ γ₂ : Γ₂) where

      base-dec : DecEq (Γ₁ × Γ₂)
      base-dec = ×-dec dec₁ dec₂

      d₁ : ShapeData (A₁ γ₁)
      d₁ = Fibre.fibre-data fe dec₁ K₁ γ₁

      d₂ : ShapeData (A₂ γ₂)
      d₂ = Fibre.fibre-data fe dec₂ K₂ γ₂

      d₁₂ : ShapeData (A₁ γ₁ × A₂ γ₂)
      d₁₂ = Fibre.fibre-data fe base-dec K₁₂ (γ₁ , γ₂)

      private
        over : (z : ʃ s₁₂) → p₁₂ z ≡ (γ₁ , γ₂)
             → (p₁ (F₁ z) , p₂ (F₂ z)) ≡ (γ₁ , γ₂)
        over z e = sym (square z) ∙ e

      -- The map that the comparison of the totals induces on the fibres.
      on-fibres : ʃ d₁₂ → ʃ d₁ × ʃ d₂
      on-fibres w =
        (F₁ (fst w) , ap fst (over (fst w) (snd w))) ,
        (F₂ (fst w) , ap snd (over (fst w) (snd w)))

      private
        first-on-units : (a : A₁ γ₁ × A₂ γ₂)
          → first d₁ d₂ d₁₂ (η d₁₂ a) ≡ fst (on-fibres (η d₁₂ a))
        first-on-units a =
          rec-η d₁₂ (ʃ d₁) (ʃ-set d₁) (ʃ-discrete d₁) (λ q → η d₁ (fst q)) a
          ∙ fiber-path (sym (F₁-η ((γ₁ , fst a) , (γ₂ , snd a))))
                       (Γ₁-set _ _ _ _)

        second-on-units : (a : A₁ γ₁ × A₂ γ₂)
          → second d₁ d₂ d₁₂ (η d₁₂ a) ≡ snd (on-fibres (η d₁₂ a))
        second-on-units a =
          rec-η d₁₂ (ʃ d₂) (ʃ-set d₂) (ʃ-discrete d₂) (λ q → η d₂ (snd q)) a
          ∙ fiber-path (sym (F₂-η ((γ₁ , fst a) , (γ₂ , snd a))))
                       (Γ₂-set _ _ _ _)

      -- The canonical comparison of the fibre data IS that map. Uniqueness
      -- for d₁₂; every argument is crisp, and no product axiom is used.
      canonical : (w : ʃ d₁₂) → compare d₁ d₂ d₁₂ w ≡ on-fibres w
      canonical w = pair-path
        (unique d₁₂ (ʃ d₁) (ʃ-set d₁) (ʃ-discrete d₁)
           (first d₁ d₂ d₁₂) (λ v → fst (on-fibres v)) first-on-units w)
        (unique d₁₂ (ʃ d₂) (ʃ-set d₂) (ʃ-discrete d₂)
           (second d₁ d₂ d₁₂) (λ v → snd (on-fibres v)) second-on-units w)

      ------------------------------------------------------------------
      -- With the product axiom for the totals, an ordinary hypothesis.

      module _ (pp : PreservesProduct s₁ s₂ s₁₂) where

        private
          inv : ʃ d₁ × ʃ d₂ → ʃ d₁₂
          inv w =
            inverse pp u ,
            ( square (inverse pp u)
            ∙ pair-path (ap p₁ (ap fst (section pp u)) ∙ snd (fst w))
                        (ap p₂ (ap snd (section pp u)) ∙ snd (snd w)) )
            where
            u : ʃ s₁ × ʃ s₂
            u = fst (fst w) , fst (snd w)

          section-law : (w : ʃ d₁ × ʃ d₂) → on-fibres (inv w) ≡ w
          section-law w = pair-path
            (fiber-path (ap fst (section pp u)) (Γ₁-set _ _ _ _))
            (fiber-path (ap snd (section pp u)) (Γ₂-set _ _ _ _))
            where
            u : ʃ s₁ × ʃ s₂
            u = fst (fst w) , fst (snd w)

          retraction-law : (w : ʃ d₁₂) → inv (on-fibres w) ≡ w
          retraction-law w =
            fiber-path (retraction pp (fst w)) (base-set _ _ _ _)

        -- The product law for the fibres at (γ₁ , γ₂).
        fibre-product : PreservesProduct d₁ d₂ d₁₂
        fibre-product = set-equiv (×-set (ʃ-set d₁) (ʃ-set d₂)) inv
          (λ w → canonical (inv w) ∙ section-law w)
          (λ w → ap inv (canonical w) ∙ retraction-law w)

        -- The product law for ANY terminal shape data of the three types
        -- (GlobalChoice.ProductChoice: the law does not depend on the
        -- choice). This is the form to use from another module: its type
        -- mentions only the data that the caller supplies.
        product-for : (@♭ t₁ : ShapeData (A₁ γ₁)) (@♭ t₂ : ShapeData (A₂ γ₂))
                      (@♭ t₁₂ : ShapeData (A₁ γ₁ × A₂ γ₂))
                    → PreservesProduct t₁ t₂ t₁₂
        product-for t₁ t₂ t₁₂ =
          ProductChoice.transport-product d₁ t₁ d₂ t₂ d₁₂ t₁₂ fibre-product
