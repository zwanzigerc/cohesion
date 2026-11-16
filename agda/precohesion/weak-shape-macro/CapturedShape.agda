{-# OPTIONS --cohesion --without-K --flat-split #-}

-- An automatically captured shape carries its original whole-context data.
-- It does not give a new pointwise reflection property for the selected fiber.
module CapturedShape where

open import Foundations
open import RelativeSliceShape using (RelativeShapeOver)
import RelativeSliceShape as Relative

SourceSection : {@♭ a ℓ : Level}
              → (@♭ A : Set a) (@♭ B : Set ℓ)
              → (@♭ embed : A → B) (@♭ decode : B → A)
              → Set a
SourceSection A B embed decode = (x : A) → decode (embed x) ≡ x

SourceRetraction : {@♭ a ℓ : Level}
                 → (@♭ A : Set a) (@♭ B : Set ℓ)
                 → (@♭ embed : A → B) (@♭ decode : B → A)
                 → Set ℓ
SourceRetraction A B embed decode = (x : B) → embed (decode x) ≡ x

data CapturedShape {@♭ a ℓ : Level} (@♭ A : Set a) : Set (lsuc (a ⊔ ℓ)) where
  captured : (@♭ Context : Set ℓ)
           → (@♭ context-discrete : Discrete Context)
           → (@♭ Family : Context → Set ℓ)
           → (@♭ shaped : RelativeShapeOver Context context-discrete Family)
           → (@♭ point : Context)
           → (@♭ embed : A → Family point)
           → (@♭ decode : Family point → A)
           → (@♭ section : SourceSection A (Family point) embed decode)
           → (@♭ retraction : SourceRetraction A (Family point) embed decode)
           → CapturedShape {ℓ = ℓ} A

module Output {@♭ a ℓ : Level} {@♭ A : Set a} where

  context : (@♭ s : CapturedShape {ℓ = ℓ} A) → Set ℓ
  context (captured Context _ _ _ _ _ _ _ _) = Context

  context-discrete : (@♭ s : CapturedShape {ℓ = ℓ} A) → Discrete (context s)
  context-discrete (captured _ cd _ _ _ _ _ _ _) x = cd x

  family : (@♭ s : CapturedShape {ℓ = ℓ} A) → context s → Set ℓ
  family (captured _ _ Family _ _ _ _ _ _) γ = Family γ

  whole-context : (@♭ s : CapturedShape {ℓ = ℓ} A)
                → RelativeShapeOver (context s) (context-discrete s) (family s)
  whole-context (captured _ _ _ shaped _ _ _ _ _) = shaped

  point : (@♭ s : CapturedShape {ℓ = ℓ} A) → context s
  point (captured _ _ _ _ p _ _ _ _) = p

  source-embed : (@♭ s : CapturedShape {ℓ = ℓ} A) → A → family s (point s)
  source-embed (captured _ _ _ _ _ embed _ _ _) x = embed x

  source-decode : (@♭ s : CapturedShape {ℓ = ℓ} A) → family s (point s) → A
  source-decode (captured _ _ _ _ _ _ decode _ _) x = decode x

  source-section : (@♭ s : CapturedShape {ℓ = ℓ} A)
                 → SourceSection A (family s (point s)) (source-embed s) (source-decode s)
  source-section (captured _ _ _ _ _ _ _ section _) x = section x

  source-retraction : (@♭ s : CapturedShape {ℓ = ℓ} A)
                    → SourceRetraction A (family s (point s)) (source-embed s) (source-decode s)
  source-retraction (captured _ _ _ _ _ _ _ _ retraction) x = retraction x

  carrier : (@♭ s : CapturedShape {ℓ = ℓ} A) → Set ℓ
  carrier s = Relative.Output.family (whole-context s) (point s)

  unit : (@♭ s : CapturedShape {ℓ = ℓ} A) → A → carrier s
  unit s a = Relative.Output.family-unit (whole-context s) (point s) (source-embed s a)

  carrier-set : (@♭ s : CapturedShape {ℓ = ℓ} A) → IsSet (carrier s)
  carrier-set s x y p q = Relative.Output.family-set (whole-context s) (point s) x y p q

