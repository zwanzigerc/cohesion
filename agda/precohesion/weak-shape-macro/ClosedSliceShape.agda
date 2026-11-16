{-# OPTIONS --cohesion --without-K --flat-split #-}

module ClosedSliceShape where

open import Foundations

-- Native maps over a fixed native base. No encoded type theory is involved.
record MapOver {Γ X Y : Set} (p : X → Γ) (q : Y → Γ) : Set where
  constructor over-map
  field
    function : X → Y
    triangle : (x : X) → q (function x) ≡ p x
open MapOver public

UnitOver : (@♭ Γ : Set) (@♭ A : Γ → Set) (@♭ S : Set)
         → (@♭ p : S → Γ) (@♭ η : Σ Γ A → S) → Set
UnitOver Γ A S p η = (a : Σ Γ A) → p (η a) ≡ fst a

-- This is a TYPE OF DATA, not a global operation producing those data.
-- The generating declaration in ClosedSliceExamples only inhabits it for
-- closed native Γ and A. No axiom ∀ Γ A → ClosedShapeOver Γ A is supplied.
precomposeOver : (@♭ Γ : Set) (@♭ A : Γ → Set)
               → (@♭ S : Set) (@♭ p : S → Γ)
               → (@♭ η : Σ Γ A → S)
               → (@♭ η-over : (a : Σ Γ A) → p (η a) ≡ fst a)
               → (@♭ D : Set) (@♭ q : D → Γ)
               → MapOver p q → MapOver (fst {B = A}) q
precomposeOver Γ A S p η η-over D q f = over-map
  (function f ∘ η)
  (λ a → triangle f (η a) ∙ η-over a)

SliceUniversal : (@♭ Γ : Set) (@♭ A : Γ → Set)
               → (@♭ S : Set) (@♭ p : S → Γ)
               → (@♭ η : Σ Γ A → S)
               → (@♭ η-over : (a : Σ Γ A) → p (η a) ≡ fst a)
               → Set₁
SliceUniversal Γ A S p η η-over =
  (@♭ D : Set) → (@♭ D-set : IsSet D) → (@♭ D-discrete : Discrete D)
  → (@♭ q : D → Γ)
  → IsEquiv (flat-map (precomposeOver Γ A S p η η-over D q))

-- Crisp constructor fields are used because Agda 2.8 does not allow crisp
-- record fields. This is merely a bundle of data, with native types inside.
data ClosedShapeOver
  (@♭ Γ : Set)
  (@♭ Γ-set : IsSet Γ)
  (@♭ Γ-discrete : Discrete Γ)
  (@♭ A : Γ → Set) : Set₁ where
  shape-over : (@♭ S : Set)
             → (@♭ S-set : IsSet S)
             → (@♭ S-discrete : Discrete S)
             → (@♭ p : S → Γ)
             → (@♭ η : Σ Γ A → S)
             → (@♭ η-over : UnitOver Γ A S p η)
             → (@♭ universal : SliceUniversal Γ A S p η η-over)
             → ClosedShapeOver Γ Γ-set Γ-discrete A

module Output
  {@♭ Γ : Set} {@♭ Γ-set : IsSet Γ} {@♭ Γ-discrete : Discrete Γ}
  {@♭ A : Γ → Set} where

  Total : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A) → Set
  Total (shape-over S _ _ _ _ _ _) = S

  projection : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A) → Total s → Γ
  projection (shape-over _ _ _ p _ _ _) x = p x

  unit : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A) → Σ Γ A → Total s
  unit (shape-over _ _ _ _ η _ _) x = η x

  unit-over : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A)
            → (a : Σ Γ A) → projection s (unit s a) ≡ fst a
  unit-over (shape-over _ _ _ _ _ η-over _) x = η-over x

  total-set : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A) → IsSet (Total s)
  total-set (shape-over _ S-set _ _ _ _ _) x y p q = S-set x y p q

  total-discrete : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A) → Discrete (Total s)
  total-discrete (shape-over _ _ S-discrete _ _ _ _) x = S-discrete x

  universal : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A)
            → SliceUniversal Γ A (Total s) (projection s) (unit s) (unit-over s)
  universal (shape-over _ _ _ _ _ _ up) D ds dd q f = up D ds dd q f

  factor : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A)
         → (@♭ D : Set) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
         → (@♭ q : D → Γ) (@♭ f : MapOver (fst {B = A}) q)
         → MapOver (projection s) q
  factor s D D-set D-discrete q f =
    counit (inverse (universal s D D-set D-discrete q) (box f))

  factor-β : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A)
           → (@♭ D : Set) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
           → (@♭ q : D → Γ) (@♭ f : MapOver (fst {B = A}) q)
           → precomposeOver Γ A (Total s) (projection s) (unit s) (unit-over s) D q
               (factor s D D-set D-discrete q f) ≡ f
  factor-β s D D-set D-discrete q f =
    sym (flat-map-counit
      (precomposeOver Γ A (Total s) (projection s) (unit s) (unit-over s) D q)
      (inverse (universal s D D-set D-discrete q) (box f)))
    ∙ ap counit (section (universal s D D-set D-discrete q) (box f))

  factor-on-unit : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A)
                 → (@♭ D : Set) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
                 → (@♭ q : D → Γ) (@♭ f : MapOver (fst {B = A}) q)
                 → (a : Σ Γ A)
                 → function (factor s D D-set D-discrete q f) (unit s a)
                   ≡ function f a
  factor-on-unit s D D-set D-discrete q f a =
    happly (ap function (factor-β s D D-set D-discrete q f)) a

  -- This dependent native family is the output over Γ. There is deliberately
  -- no field asserting that each value reflects A γ pointwise.
  family : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A) → Γ → Set
  family s γ = Fiber (projection s) γ

  family-unit : (@♭ s : ClosedShapeOver Γ Γ-set Γ-discrete A)
              → (γ : Γ) → A γ → family s γ
  family-unit s γ a = unit s (γ , a) , unit-over s (γ , a)
