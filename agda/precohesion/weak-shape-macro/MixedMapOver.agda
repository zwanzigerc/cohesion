{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Maps over a base whose source, target and base live at DIFFERENT levels,
-- and their comparison with the same-level maps of RelativeSliceShape.
-- Claude (Fable), 13 November 2026; after fable-impl-15 (HANDOFF-32;
-- RELATIVE-LARGE-UP-IMPLEMENTATION-REVIEW-01 section 2 and section 4).
-- Postulate-free; no function extensionality; no reflection; no shape.
--
-- WHY SEPARATE RECORDS. RelativeSliceShape.MapOver and SetFibers have one
-- level for base, source and target. A slice map from a small source into
-- a target of a larger universe is not one of them. Of the two ways to
-- get it, generalising the old record or adding a mixed one beside it,
-- this tree takes the SECOND:
--   * RelativeSliceShape is the first module of the tree. The type
--     RelativeShapeOver, which every capture declares an inhabitant of
--     and every relative reflection is, is DEFINED with MapOver and
--     SetFibers at one level, and eleven further modules use the
--     record directly. A record with three levels there would put a
--     changed definition under every statement accepted so far and
--     change the inference of levels at each of those uses. It stays
--     byte-identical;
--   * the mixed record is used in one theorem (RelativeLargeTarget).
-- The price is that the two records have to be compared. That is done
-- here, field by field, at one level:
--   to-old, from-old      the two maps between the records
--   to-from, from-to      both round trips, by computation (records have η)
--   same-set-fibers       SetFibersM at one level IS SetFibers
--   precompose-square,    the two precompositions commute with to-old and
--   precompose-square′    with from-old, by computation
-- So at one level the mixed precomposition is the old one conjugated by a
-- pair of mutually inverse maps. Nothing here says anything about a
-- universal property; RelativeLargeTarget.SameLevel transfers one.
--
--   MapOverM r q          a map X → D with q ∘ function ≡ r pointwise,
--                         for Γ : Set b, X : Set x, D : Set y
--   SetFibersM q          every fibre of q : D → Γ is a set
--   precomposeOverM       precomposition with a unit over the base: the
--                         formula of RelativeSliceShape.precomposeOver,
--                         for a target of Set (ℓ ⊔ L)
--   set-fibers-between-sets   a map from a set to a set has set fibres
module MixedMapOver where

open import Foundations
open import RelativeSliceShape
  using (MapOver; over-map; function; triangle; UnitOver; SetFibers;
         precomposeOver)
open import TotalBridge using (Σ-set)

record MapOverM {b x y : Level} {Γ : Set b} {X : Set x} {D : Set y}
                (r : X → Γ) (q : D → Γ) : Set (b ⊔ x ⊔ y) where
  constructor over-mapM
  field
    functionM : X → D
    triangleM : (x : X) → q (functionM x) ≡ r x
open MapOverM public

SetFibersM : {@♭ b d : Level} {@♭ Γ : Set b} {@♭ D : Set d}
           → (@♭ q : D → Γ) → Set (b ⊔ d)
SetFibersM {Γ = Γ} q = (γ : Γ) → IsSet (Fiber q γ)

-- The formula of precomposeOver. The source, its base, the carrier, the
-- projection and the unit are at level ℓ and are not raised; only the
-- target is at ℓ ⊔ L.
precomposeOverM : {@♭ ℓ : Level} (@♭ L : Level)
                → (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ)
                → (@♭ S : Set ℓ) (@♭ p : S → Γ)
                → (@♭ η : Σ Γ A → S)
                → (@♭ η-over : UnitOver Γ A S p η)
                → (@♭ D : Set (ℓ ⊔ L)) (@♭ q : D → Γ)
                → MapOverM p q → MapOverM (fst {B = A}) q
precomposeOverM L Γ A S p η η-over D q k = over-mapM
  (λ a → functionM k (η a))
  (λ a → triangleM k (η a) ∙ η-over a)

------------------------------------------------------------------------
-- At one level.

module _ {ℓ : Level} {Γ X D : Set ℓ} {r : X → Γ} {q : D → Γ} where

  to-old : MapOverM r q → MapOver r q
  to-old k = over-map (functionM k) (triangleM k)

  from-old : MapOver r q → MapOverM r q
  from-old k = over-mapM (function k) (triangle k)

  to-from : (k : MapOver r q) → to-old (from-old k) ≡ k
  to-from k = refl

  from-to : (k : MapOverM r q) → from-old (to-old k) ≡ k
  from-to k = refl

same-set-fibers : {@♭ ℓ : Level} {@♭ Γ D : Set ℓ} (@♭ q : D → Γ)
                → SetFibersM q ≡ SetFibers q
same-set-fibers q = refl

module _ {@♭ ℓ : Level}
  (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ) (@♭ S : Set ℓ) (@♭ p : S → Γ)
  (@♭ η : Σ Γ A → S) (@♭ η-over : UnitOver Γ A S p η)
  (@♭ D : Set ℓ) (@♭ q : D → Γ) where

  -- The ceiling ℓ ⊔ lzero is ℓ.
  precompose-square : (k : MapOverM p q)
    → to-old (precomposeOverM lzero Γ A S p η η-over D q k)
      ≡ precomposeOver Γ A S p η η-over D q (to-old k)
  precompose-square k = refl

  precompose-square′ : (k : MapOver p q)
    → precomposeOverM lzero Γ A S p η η-over D q (from-old k)
      ≡ from-old (precomposeOver Γ A S p η η-over D q k)
  precompose-square′ k = refl

------------------------------------------------------------------------
-- A map between sets has set fibres: a fibre is a Σ of the source with
-- paths of the base, and paths in a set are a proposition.

private
  cancel : ∀ {a} {A : Set a} {x y : A} (c : x ≡ y) → sym c ∙ c ≡ refl
  cancel refl = refl

  prop-set : ∀ {a} {A : Set a} → IsProp A → IsSet A
  prop-set {A = A} h x y p q = normal p ∙ sym (normal q)
    where
    normal : {y : A} (r : x ≡ y) → r ≡ sym (h x x) ∙ h x y
    normal refl = sym (cancel (h x x))

set-fibers-between-sets :
  {@♭ b d : Level} {@♭ Γ : Set b} {@♭ D : Set d}
  → IsSet Γ → IsSet D → (@♭ q : D → Γ) → SetFibersM q
set-fibers-between-sets Γ-set D-set q γ =
  Σ-set D-set (λ y → prop-set (Γ-set (q y) γ))
