{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Restricting a whole reflection to one fibre of a decidable context.
-- Postulate-free. Claude (Fable), 13 November 2026; fable-impl-10.
-- FABLE05-ASSEMBLY-REVIEW-01 section 3 ("the fibre-total identifications
-- at g₀ and the local relative payloads obtained by the justified
-- bridges"); HANDOFF-17 section 3, field B9.
--
-- Data, all crisp: a discrete G with DECIDABLE equality (the packed
-- context); a family C of discrete SETS over it (the local bases; NO
-- decidability is asked of them); a family A over Σ G C; terminal shape
-- data ŝ of the whole total source Σ (Σ G C) A. Then, by bridges that
-- already exist (the whole constructions retain the carrier and unit of
-- ŝ; the local ones retain its actual fibre over g₀ and the fibre unit):
--
--   whole            the relative reflection of A over Σ G C   (TotalConverse)
--   over-context     the relative reflection over G of the local total
--                    sources  Local g = Σ (C g) (λ c → A (g , c))
--                                                  (Along, TotalConverse)
--   AtPoint.local-data   at a crisp g₀: terminal shape data of Local g₀,
--                        carried by the fibre of ʃ ŝ over g₀
--                                                  (DecidableBase.Fibre)
--   AtPoint.restricted   the relative reflection over C g₀ of the family
--                        c ↦ A (g₀ , c), with that carrier  (TotalConverse)
--
-- and for the inclusion  c ↦ (g₀ , c)  of the fibre C g₀ into Σ G C:
--
--   AtPoint.explicit, canonical   the canonical comparison along the
--                             inclusion, written out: it transports the
--                             C-component of the whole projection into
--                             C g₀ and keeps the point of ʃ ŝ
--   AtPoint.under             so it does not move the underlying point
--   AtPoint.inclusion-total   it is an equivalence (total form)
--   AtPoint.inclusion-fibres  it is an equivalence in every fibre
--
-- So `restricted` IS the whole reflection pulled back to the fibre of the
-- context, and the identification is the canonical comparison, not a
-- chosen equivalence of carriers.
--
-- What is and is not used. Decidability of G is used once, inside
-- DecidableBase.Fibre, to make the fibre over g₀ a terminal reflection.
-- The inverse of the comparison is written down explicitly and its two
-- laws are equalities of points of sets (G and Σ G C are sets). No product
-- law, Nullstellensatz or continuity. This is NOT a statement that shape
-- commutes with the pullback along an arbitrary map into Σ G C: the map
-- here is the inclusion of a fibre over a decidable point of G, a
-- complemented subobject. For maps between the local bases themselves
-- nothing is claimed (see ContextSpecialisation).
--
-- Spelling. The inclusion is written as the lambda  λ c → g₀ , c  at every
-- use, here and in ContextSpecialisation, and `restricted` is exported by
-- renaming, not defined. Both are deliberate: a named inclusion is stored
-- by the compiler sometimes as the name and sometimes as this lambda,
-- depending on the types of the neighbouring module arguments, and a
-- second definition of `restricted` is a second spelling. Two spellings of
-- a reflection that is derived through four bridges are expensive to
-- compare (FABLE-IMPL-10.txt, section on cost). A client that restates
-- results about these reflections in its own terms should seal them first
-- (Sealed).
module DecidableRestriction where

open import Foundations
open import RelativeSliceShape
open import PullbackSetFibers using (transport)
open import FlatContext using (fiber-path)
open import ShapeChoice using (FunExtAt)
open import ShapeElim using (module SigmaDiscrete)
open import Adjointify using (quasi-inverse)
open import GlobalPrecohesion
open import GlobalChoice using (module Along)
open import DecidableBase using (DecEq; decidable-set; module Fibre)
open import TotalBridge using (Σ-set)
open import TotalConverse using (module Converse)
open import ComparisonRecognition using (module Recognise)

private
  Σ-path : ∀ {a b} {X : Set a} {Y : X → Set b}
         → {x x′ : X} {y : Y x} {y′ : Y x′}
         → (q : x ≡ x′) → transport Y q y ≡ y′
         → _≡_ {A = Σ X Y} (x , y) (x′ , y′)
  Σ-path refl refl = refl

module _ {@♭ ℓ : Level} where

  module Restrict
    (@♭ fe : FunExtAt ℓ)
    {@♭ G : Set ℓ} {@♭ dG : Discrete G} (@♭ dec : DecEq G)
    {@♭ C : G → Set ℓ}
    (@♭ dC : (@♭ g : G) → Discrete (C g))
    (@♭ C-set : (g : G) → IsSet (C g))
    {@♭ A : Σ G C → Set ℓ}
    (@♭ ŝ : ShapeData (Σ (Σ G C) A)) where

    G-set : IsSet G
    G-set = decidable-set dec

    base-discrete : Discrete (Σ G C)
    base-discrete = SigmaDiscrete.discrete dG dC

    base-set : IsSet (Σ G C)
    base-set = Σ-set G-set C-set

    -- The whole reflection, with the carrier and the unit of ŝ.
    whole : RelativeShapeOver (Σ G C) base-discrete A
    whole = Converse.relative fe {dΓ = base-discrete} base-set ŝ

    -- The local total sources, as a family over the context.
    Local : G → Set ℓ
    Local g = Σ (C g) (λ c → A (g , c))

    private
      assoc : Σ (Σ G C) A → Σ G Local
      assoc x = fst (fst x) , (snd (fst x) , snd x)

      unassoc : Σ G Local → Σ (Σ G C) A
      unassoc y = (fst y , fst (snd y)) , snd (snd y)

    over-context-data : ShapeData (Σ G Local)
    over-context-data = Along.along assoc unassoc (λ _ → refl) (λ _ → refl) ŝ

    over-context : RelativeShapeOver G dG Local
    over-context = Converse.relative fe {dΓ = dG} G-set over-context-data

    private
      S : Set ℓ
      S = ʃ ŝ

      -- The two projections of the one carrier.
      p̂ : S → Σ G C
      p̂ = Output.projection whole

      π : S → G
      π = Output.projection over-context

      -- They agree over G. Uniqueness for ŝ at the target G.
      π-p̂ : (z : S) → π z ≡ fst (p̂ z)
      π-p̂ = unique ŝ G G-set dG π (λ z → fst (p̂ z))
        (λ x → Output.unit-over over-context (assoc x)
             ∙ sym (ap fst (Output.unit-over whole x)))

    module AtPoint (@♭ g₀ : G) where

      -- Terminal shape data of the local total source at g₀. Its carrier
      -- is the fibre of S over g₀ and its unit is the unit of ŝ.
      local-data : ShapeData (Local g₀)
      local-data = Fibre.fibre-data fe dec over-context g₀

      private
        module Rec = Recognise fe (Σ G C) (C g₀) base-discrete (dC g₀)
          (C-set g₀) A (λ c → g₀ , c) whole local-data

      -- restricted : RelativeShapeOver (C g₀) (dC g₀) (A ∘ (λ c → g₀ , c))
      -- The whole reflection restricted to the fibre of the context: the
      -- relative reflection over C g₀ with the carrier and unit of
      -- local-data (TotalConverse). Exported under this name, not defined
      -- again, so that every user spells it in one way.
      open Rec public using () renaming (reflection to restricted)

      -- The canonical comparison along the inclusion of the fibre.
      module Inclusion = Rec.Form

      -- An explicit description of that comparison. A point of the fibre
      -- of S over g₀ is a point z of S with a path e : π z ≡ g₀. Its image
      -- under the whole projection lies over g₀, so its second component
      -- can be transported into C g₀.
      lies : (w : ʃ local-data) → fst (p̂ (fst w)) ≡ g₀
      lies w = sym (π-p̂ (fst w)) ∙ snd w

      explicit : ʃ local-data → Inclusion.PulledTotal
      explicit w = transport C (lies w) (snd (p̂ (fst w)))
                 , (fst w , Σ-path (lies w) refl)

      private
        -- A point of Σ G C that is equal to (g₀ , c) has second component
        -- c, along whichever path its first component is moved to g₀.
        over-point : {y : Σ G C} {c : C g₀} → y ≡ (g₀ , c)
                   → (l : fst y ≡ g₀) → transport C l (snd y) ≡ c
        over-point {c = c} refl l =
          ap (λ r → transport C r c) (G-set g₀ g₀ l refl)

        -- Two points of the pulled-back total space with equal components
        -- are equal: the remaining datum is a path in the set Σ G C.
        pulled-path : {c c′ : C g₀} → c′ ≡ c → {z z′ : S} → z′ ≡ z
                    → {e′ : p̂ z′ ≡ (g₀ , c′)} {e : p̂ z ≡ (g₀ , c)}
                    → _≡_ {A = Inclusion.PulledTotal}
                        (c′ , (z′ , e′)) (c , (z , e))
        pulled-path {c} refl {z} refl {e′} {e} =
          ap (λ r → c , (z , r)) (base-set _ _ e′ e)

        explicit-η : (x : Local g₀)
                   → explicit (η local-data x) ≡ function Inclusion.pulled-unit x
        explicit-η x = pulled-path
          (over-point (Output.unit-over whole ((g₀ , fst x) , snd x))
                      (lies (η local-data x)))
          refl

        inv : Inclusion.PulledTotal → ʃ local-data
        inv v = fst (snd v) , (π-p̂ (fst (snd v)) ∙ ap fst (snd (snd v)))

        ret : (w : ʃ local-data) → inv (explicit w) ≡ w
        ret w = fiber-path refl (G-set _ _ _ _)

        sec : (v : Inclusion.PulledTotal) → explicit (inv v) ≡ v
        sec v = pulled-path (over-point (snd (snd v)) (lies (inv v))) refl

        explicit-equivalence : IsEquiv explicit
        explicit-equivalence = quasi-inverse inv sec ret

      -- The canonical comparison IS the explicit map.
      canonical : (w : ʃ local-data) → Inclusion.comparison-total w ≡ explicit w
      canonical = Rec.canonical explicit explicit-η

      -- In particular it keeps the underlying point of the carrier S.
      under : (w : ʃ local-data)
            → fst (snd (Inclusion.comparison-total w)) ≡ fst w
      under w = ap (λ v → fst (snd v)) (canonical w)

      -- The canonical comparison along the inclusion is an equivalence.
      inclusion-total : Inclusion.TotalComparisonIsEquivalence
      inclusion-total = Rec.total explicit explicit-η explicit-equivalence

      inclusion-fibres : Inclusion.ComparisonIsEquivalence
      inclusion-fibres = Inclusion.FromTotal.fibres (C-set g₀) inclusion-total
