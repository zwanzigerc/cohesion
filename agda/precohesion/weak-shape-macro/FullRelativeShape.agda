{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The FULL (untruncated) relative shape of a crisp family over a crisp
-- discrete base: the interface, with nothing declared.
-- Claude (Fable), 14 November 2026; fable-impl-23 (HANDOFF-38; the
-- proposal of HIGHER-RESEARCH-FABLE-01 and the calculation of
-- FULL-SHAPE-CAPTURE-AND-LEVELS-01).
--
-- For a crisp discrete Γ and a crisp family A over it, a full shape is
--   a discrete R,  q : R → Γ,  η : Σ Γ A → R  with  q ∘ η ∼ fst,
-- such that for EVERY crisp map t : D → Γ from a crisp discrete D,
-- precomposition with η is an equivalence
--     ♭ (MapOver q t) → ♭ (MapOver fst t)
-- of the boxed types of WHOLE maps over Γ (a function and its triangle).
--
-- It differs from RelativeSliceShape.RelativeShapeOver in two places and
-- in nothing else: q is not asked to have set fibres, and the test maps t
-- are not asked to have set fibres. So the carrier keeps the higher
-- structure of its fibres and of the base, and a test may be a map whose
-- fibres are not sets. Neither datum is a special case of the other: a
-- RelativeShapeOver has set fibres and answers set-fibred tests only.
-- FullToShape0 derives a RelativeShapeOver from a full shape.
--
-- MapOver, UnitOver and precomposeOver are those of RelativeSliceShape,
-- unchanged. The triangle of a MapOver is a pointwise path; no function
-- extensionality is used here.
--
-- Nothing is postulated and nothing is declared: a full shape is a value
-- of the data type below, supplied by whoever has one.
module FullRelativeShape where

open import Foundations
open import RelativeSliceShape
  using (MapOver; over-map; function; triangle; UnitOver; precomposeOver)
open import NativeSharp using (box-crisp-path)

FullUniversal : {@♭ ℓ : Level}
              → (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ)
              → (@♭ R : Set ℓ) (@♭ q : R → Γ)
              → (@♭ η : Σ Γ A → R)
              → (@♭ η-over : UnitOver Γ A R q η)
              → Set (lsuc ℓ)
FullUniversal Γ A R q η η-over =
  (@♭ D : Set _) → (@♭ D-discrete : Discrete D) → (@♭ t : D → Γ)
  → IsEquiv (flat-map (precomposeOver Γ A R q η η-over D t))

-- Crisp constructor fields, as in RelativeSliceShape.
data FullShapeOver
  {@♭ ℓ : Level}
  (@♭ Γ : Set ℓ)
  (@♭ Γ-discrete : Discrete Γ)
  (@♭ A : Γ → Set ℓ) : Set (lsuc ℓ) where
  full-shape : (@♭ R : Set ℓ)
             → (@♭ R-discrete : Discrete R)
             → (@♭ q : R → Γ)
             → (@♭ η : Σ Γ A → R)
             → (@♭ η-over : UnitOver Γ A R q η)
             → (@♭ universal : FullUniversal Γ A R q η η-over)
             → FullShapeOver Γ Γ-discrete A

module FullOutput
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ Γ-discrete : Discrete Γ}
  {@♭ A : Γ → Set ℓ} where

  Total : (@♭ s : FullShapeOver Γ Γ-discrete A) → Set ℓ
  Total (full-shape R _ _ _ _ _) = R

  projection : (@♭ s : FullShapeOver Γ Γ-discrete A) → Total s → Γ
  projection (full-shape _ _ q _ _ _) x = q x

  unit : (@♭ s : FullShapeOver Γ Γ-discrete A) → Σ Γ A → Total s
  unit (full-shape _ _ _ η _ _) x = η x

  unit-over : (@♭ s : FullShapeOver Γ Γ-discrete A)
            → UnitOver Γ A (Total s) (projection s) (unit s)
  unit-over (full-shape _ _ _ _ η-over _) x = η-over x

  total-discrete : (@♭ s : FullShapeOver Γ Γ-discrete A)
                 → Discrete (Total s)
  total-discrete (full-shape _ rd _ _ _ _) x = rd x

  -- The fibres. They are not asked to be sets.
  family : (@♭ s : FullShapeOver Γ Γ-discrete A) → Γ → Set ℓ
  family s γ = Fiber (projection s) γ

  family-unit : (@♭ s : FullShapeOver Γ Γ-discrete A)
              → (γ : Γ) → A γ → family s γ
  family-unit s γ a = unit s (γ , a) , unit-over s (γ , a)

  universal : (@♭ s : FullShapeOver Γ Γ-discrete A)
            → FullUniversal Γ A (Total s) (projection s) (unit s)
                (unit-over s)
  universal (full-shape _ _ _ _ _ up) D dd t f = up D dd t f

  -- Precomposition with the unit, on whole maps over Γ.
  pre : (@♭ s : FullShapeOver Γ Γ-discrete A)
      → (@♭ D : Set ℓ) (@♭ t : D → Γ)
      → MapOver (projection s) t → MapOver (fst {B = A}) t
  pre s D t = precomposeOver Γ A (Total s) (projection s) (unit s)
    (unit-over s) D t

  -- A crisp whole map over Γ out of the source factors through the unit.
  factor : (@♭ s : FullShapeOver Γ Γ-discrete A)
         → (@♭ D : Set ℓ) (@♭ dd : Discrete D) (@♭ t : D → Γ)
         → (@♭ f : MapOver (fst {B = A}) t) → MapOver (projection s) t
  factor s D dd t f = counit (inverse (universal s D dd t) (box f))

  -- The WHOLE map is recovered: the function and its triangle.
  factor-β : (@♭ s : FullShapeOver Γ Γ-discrete A)
           → (@♭ D : Set ℓ) (@♭ dd : Discrete D) (@♭ t : D → Γ)
           → (@♭ f : MapOver (fst {B = A}) t)
           → pre s D t (factor s D dd t f) ≡ f
  factor-β s D dd t f =
    sym (flat-map-counit (pre s D t) (inverse (universal s D dd t) (box f)))
    ∙ ap counit (section (universal s D dd t) (box f))

  factor-on-unit : (@♭ s : FullShapeOver Γ Γ-discrete A)
                 → (@♭ D : Set ℓ) (@♭ dd : Discrete D) (@♭ t : D → Γ)
                 → (@♭ f : MapOver (fst {B = A}) t)
                 → (a : Σ Γ A)
                 → function (factor s D dd t f) (unit s a) ≡ function f a
  factor-on-unit s D dd t f a =
    ap (λ h → function h a) (factor-β s D dd t f)

  factor-η : (@♭ s : FullShapeOver Γ Γ-discrete A)
           → (@♭ D : Set ℓ) (@♭ dd : Discrete D) (@♭ t : D → Γ)
           → (@♭ g : MapOver (projection s) t)
           → factor s D dd t (pre s D t g) ≡ g
  factor-η s D dd t g = ap counit (retraction (universal s D dd t) (box g))

  -- Two crisp whole maps over Γ out of the carrier with the same
  -- precomposite are equal, as whole maps.
  unique : (@♭ s : FullShapeOver Γ Γ-discrete A)
         → (@♭ D : Set ℓ) (@♭ dd : Discrete D) (@♭ t : D → Γ)
         → (@♭ g h : MapOver (projection s) t)
         → (@♭ e : pre s D t g ≡ pre s D t h) → g ≡ h
  unique s D dd t g h e =
    sym (factor-η s D dd t g)
    ∙ ap (λ z → counit (inverse (universal s D dd t) z)) (box-crisp-path e)
    ∙ factor-η s D dd t h
