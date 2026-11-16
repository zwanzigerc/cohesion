{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Native discrete telescopes used by the automatic context-capture frontend.
-- These are native datatypes, not codes for a separate type theory.
module CaptureContext where

open import Foundations
open import FlatContext using (coherent-inverse)

data CrispUnit : Set where
  end : CrispUnit

-- A terminator at a chosen universe level can raise an entire telescope to
-- the common level needed by RelativeShapeOver, without adding variables.
data CrispUnitAt (@♭ ℓ : Level) : Set ℓ where
  end-at : CrispUnitAt ℓ

data CrispΣ {@♭ a b : Level}
  (@♭ A : Set a)
  (@♭ B : (@♭ x : A) → Set b) : Set (a ⊔ b) where
  pair : (@♭ x : A) → (@♭ tail : B x) → CrispΣ A B

-- Expected crisp binders of these combinators let reflected lambdas retain
-- crisp dependency even though Agda 2.8's reflected ArgInfo omits cohesion.
unpack : {@♭ a b : Level} {c : Level}
       → {@♭ A : Set a} {@♭ B : (@♭ x : A) → Set b} {C : Set c}
       → ((@♭ x : A) → (@♭ tail : B x) → C)
       → CrispΣ A B → C
unpack f (pair x tail) = f x tail

unpack-dependent : {@♭ a b : Level} {c : Level}
                 → {@♭ A : Set a} {@♭ B : (@♭ x : A) → Set b}
                 → (C : CrispΣ A B → Set c)
                 → ((@♭ x : A) → (@♭ tail : B x) → C (pair x tail))
                 → (z : CrispΣ A B) → C z
unpack-dependent C f (pair x tail) = f x tail

unpack-unit : ∀ {c} {C : Set c} → C → CrispUnit → C
unpack-unit value end = value

unpack-unit-dependent : ∀ {c} (C : CrispUnit → Set c)
                      → C end → (z : CrispUnit) → C z
unpack-unit-dependent C value end = value

unpack-unit-at : {@♭ ℓ : Level} {c : Level} {C : Set c}
               → C → CrispUnitAt ℓ → C
unpack-unit-at value end-at = value

module _ {@♭ ℓ : Level} where
  unit-at-box : CrispUnitAt ℓ → ♭ (CrispUnitAt ℓ)
  unit-at-box end-at = box end-at

  unit-at-section : (x : CrispUnitAt ℓ) → counit (unit-at-box x) ≡ x
  unit-at-section end-at = refl

  unit-at-retraction : (x : ♭ (CrispUnitAt ℓ)) → unit-at-box (counit x) ≡ x
  unit-at-retraction (box end-at) = refl

  unit-at-triangle : (x : ♭ (CrispUnitAt ℓ))
                   → ap counit (unit-at-retraction x) ≡ unit-at-section (counit x)
  unit-at-triangle (box end-at) = refl

  unit-at-discrete : Discrete (CrispUnitAt ℓ)
  unit-at-discrete = coherent-inverse unit-at-box unit-at-section
    unit-at-retraction unit-at-triangle

unit-box : CrispUnit → ♭ CrispUnit
unit-box end = box end

unit-section : (x : CrispUnit) → counit (unit-box x) ≡ x
unit-section end = refl

unit-retraction : (x : ♭ CrispUnit) → unit-box (counit x) ≡ x
unit-retraction (box end) = refl

unit-triangle : (x : ♭ CrispUnit)
              → ap counit (unit-retraction x) ≡ unit-section (counit x)
unit-triangle (box end) = refl

unit-discrete : Discrete CrispUnit
unit-discrete = coherent-inverse unit-box unit-section unit-retraction unit-triangle

module _ {@♭ a b : Level}
  {@♭ A : Set a} {@♭ B : (@♭ x : A) → Set b} where

  pair-box : CrispΣ A B → ♭ (CrispΣ A B)
  pair-box (pair x tail) = box (pair x tail)

  pair-section : (x : CrispΣ A B) → counit (pair-box x) ≡ x
  pair-section (pair x tail) = refl

  pair-retraction : (x : ♭ (CrispΣ A B)) → pair-box (counit x) ≡ x
  pair-retraction (box (pair x tail)) = refl

  pair-triangle : (x : ♭ (CrispΣ A B))
                → ap counit (pair-retraction x) ≡ pair-section (counit x)
  pair-triangle (box (pair x tail)) = refl

  telescope-discrete : Discrete (CrispΣ A B)
  telescope-discrete = coherent-inverse pair-box pair-section pair-retraction pair-triangle

-- Universe lifting makes a captured family live in the context's universe
-- without asserting resizing. The added level need not be the source level.
data Raise {@♭ a : Level} (@♭ b : Level) (A : Set a) : Set (a ⊔ b) where
  raise : A → Raise b A

lower : {@♭ a b : Level} {A : Set a} → Raise b A → A
lower (raise x) = x

raise-lower : {@♭ a b : Level} {A : Set a}
            → (x : Raise b A) → raise (lower x) ≡ x
raise-lower (raise x) = refl

lower-raise : {@♭ a b : Level} {A : Set a}
            → (x : A) → lower {b = b} (raise x) ≡ x
lower-raise x = refl

