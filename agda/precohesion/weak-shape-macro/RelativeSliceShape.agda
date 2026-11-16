{-# OPTIONS --cohesion --without-K --flat-split #-}

-- A TYPE OF whole-slice reflection data. There is deliberately no operation
-- inhabiting it uniformly for arbitrary native context/family arguments.
module RelativeSliceShape where

open import Foundations

record MapOver {ℓ : Level} {Γ X Y : Set ℓ}
               (p : X → Γ) (q : Y → Γ) : Set ℓ where
  constructor over-map
  field
    function : X → Y
    triangle : (x : X) → q (function x) ≡ p x
open MapOver public

UnitOver : {@♭ ℓ : Level} (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ)
         → (@♭ S : Set ℓ) (@♭ p : S → Γ)
         → (@♭ η : Σ Γ A → S) → Set ℓ
UnitOver Γ A S p η = (a : Σ Γ A) → p (η a) ≡ fst a

SetFibers : {@♭ ℓ : Level} {@♭ Γ S : Set ℓ}
          → (@♭ p : S → Γ) → Set ℓ
SetFibers {Γ = Γ} p = (γ : Γ) → IsSet (Fiber p γ)

precomposeOver : {@♭ ℓ : Level}
               → (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ)
               → (@♭ S : Set ℓ) (@♭ p : S → Γ)
               → (@♭ η : Σ Γ A → S)
               → (@♭ η-over : UnitOver Γ A S p η)
               → (@♭ D : Set ℓ) (@♭ q : D → Γ)
               → MapOver p q → MapOver (fst {B = A}) q
precomposeOver Γ A S p η η-over D q f = over-map
  (function f ∘ η)
  (λ a → triangle f (η a) ∙ η-over a)

SliceUniversal : {@♭ ℓ : Level}
               → (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ)
               → (@♭ S : Set ℓ) (@♭ p : S → Γ)
               → (@♭ η : Σ Γ A → S)
               → (@♭ η-over : UnitOver Γ A S p η)
               → Set (lsuc ℓ)
SliceUniversal Γ A S p η η-over =
  (@♭ D : Set _) → (@♭ D-discrete : Discrete D)
  → (@♭ q : D → Γ) → (@♭ q-set-fibers : SetFibers q)
  → IsEquiv (flat-map (precomposeOver Γ A S p η η-over D q))

-- Γ can be a higher discrete type. We require set FIBERS of p, not a set
-- total space S. This is a relative set-shape schema, and is stronger data
-- than merely specifying a set-valued reflector in the terminal context.
data RelativeShapeOver
  {@♭ ℓ : Level}
  (@♭ Γ : Set ℓ)
  (@♭ Γ-discrete : Discrete Γ)
  (@♭ A : Γ → Set ℓ) : Set (lsuc ℓ) where
  shape-over : (@♭ S : Set ℓ)
             → (@♭ S-discrete : Discrete S)
             → (@♭ p : S → Γ)
             → (@♭ p-set-fibers : SetFibers p)
             → (@♭ η : Σ Γ A → S)
             → (@♭ η-over : UnitOver Γ A S p η)
             → (@♭ universal : SliceUniversal Γ A S p η η-over)
             → RelativeShapeOver Γ Γ-discrete A

module Output
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ Γ-discrete : Discrete Γ}
  {@♭ A : Γ → Set ℓ} where

  Total : (@♭ s : RelativeShapeOver Γ Γ-discrete A) → Set ℓ
  Total (shape-over S _ _ _ _ _ _) = S

  projection : (@♭ s : RelativeShapeOver Γ Γ-discrete A) → Total s → Γ
  projection (shape-over _ _ p _ _ _ _) x = p x

  unit : (@♭ s : RelativeShapeOver Γ Γ-discrete A) → Σ Γ A → Total s
  unit (shape-over _ _ _ _ η _ _) x = η x

  unit-over : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
            → UnitOver Γ A (Total s) (projection s) (unit s)
  unit-over (shape-over _ _ _ _ _ η-over _) x = η-over x

  total-discrete : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
                 → Discrete (Total s)
  total-discrete (shape-over _ sd _ _ _ _ _) x = sd x

  family : (@♭ s : RelativeShapeOver Γ Γ-discrete A) → Γ → Set ℓ
  family s γ = Fiber (projection s) γ

  family-set : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
             → (γ : Γ) → IsSet (family s γ)
  family-set (shape-over _ _ _ pf _ _ _) γ x y p q = pf γ x y p q

  family-unit : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
              → (γ : Γ) → A γ → family s γ
  family-unit s γ a = unit s (γ , a) , unit-over s (γ , a)

  universal : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
            → SliceUniversal Γ A (Total s) (projection s) (unit s) (unit-over s)
  universal (shape-over _ _ _ _ _ _ up) D dd q qf f = up D dd q qf f

  factor : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
         → (@♭ D : Set ℓ) (@♭ dd : Discrete D)
         → (@♭ q : D → Γ) (@♭ qf : SetFibers q)
         → (@♭ f : MapOver (fst {B = A}) q) → MapOver (projection s) q
  factor s D dd q qf f =
    counit (inverse (universal s D dd q qf) (box f))

  factor-β : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
           → (@♭ D : Set ℓ) (@♭ dd : Discrete D)
           → (@♭ q : D → Γ) (@♭ qf : SetFibers q)
           → (@♭ f : MapOver (fst {B = A}) q)
           → precomposeOver Γ A (Total s) (projection s) (unit s)
               (unit-over s) D q (factor s D dd q qf f) ≡ f
  factor-β s D dd q qf f =
    sym (flat-map-counit
      (precomposeOver Γ A (Total s) (projection s) (unit s) (unit-over s) D q)
      (inverse (universal s D dd q qf) (box f)))
    ∙ ap counit (section (universal s D dd q qf) (box f))

  factor-on-unit : (@♭ s : RelativeShapeOver Γ Γ-discrete A)
                 → (@♭ D : Set ℓ) (@♭ dd : Discrete D)
                 → (@♭ q : D → Γ) (@♭ qf : SetFibers q)
                 → (@♭ f : MapOver (fst {B = A}) q)
                 → (a : Σ Γ A)
                 → function (factor s D dd q qf f) (unit s a) ≡ function f a
  factor-on-unit s D dd q qf f a =
    ap (λ h → function h a) (factor-β s D dd q qf f)

