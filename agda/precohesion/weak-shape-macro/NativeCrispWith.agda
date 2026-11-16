{-# OPTIONS --cohesion --without-K --flat-split #-}

-- NATIVE FACTS, no frontend module imported (FABLE-REVIEW-03.txt, section
-- 2.6). Expected: ACCEPTED by Agda 2.9.0-rc3. With-abstraction works in a
-- context of crisp variables, for a crisp, an ordinary and a closed
-- scrutinee, also when the result type takes a crisp argument, provided no
-- crisp implicit of that type is left undetermined
-- (NativeWithImplicitLevel.agda.fail).
module NativeCrispWith where
open import Foundations
open import Agda.Builtin.Bool using (Bool; true; false)

postulate
  P : {@♭ ℓ : Level} (@♭ A : Set) → Set ℓ
  p : {@♭ ℓ : Level} (@♭ A : Set) → P {ℓ} A

crisp-scrutinee : (@♭ A : Set) (@♭ b : Bool) → P {lzero} A
crisp-scrutinee A b with b
... | true = p A
... | false = p A

ordinary-scrutinee : (@♭ A : Set) (c : Bool) → P {lzero} A
ordinary-scrutinee A c with c
... | true = p A
... | false = p A

closed-scrutinee : (@♭ A : Set) → P {lzero} A
closed-scrutinee A with true
... | true = p A
... | false = p A

into-a-universe : (@♭ A : Set) (@♭ b : Bool) → Set
into-a-universe A b with b
... | true = A
... | false = A
