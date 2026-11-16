{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Independence of the choice of shape data. Postulate-free; no function
-- extensionality. Claude (Fable), 13 November 2026; fable-impl-02.
--
-- Two shape data s, t for the same type are related by the canonical maps
-- `across`, which preserve the units and are mutually inverse. Product
-- preservation and the Nullstellensatz are transported along them. So a
-- product or Nullstellensatz declaration made for one choice of shapes
-- serves every other choice, and two independently generated declarations
-- never have to be identified definitionally (HANDOFF-04, item (a)).
module GlobalChoice where

open import Foundations
open import FlatContext using (fiber-path)
open import GlobalPrecohesion

------------------------------------------------------------------------
-- Two facts about sets.

-- A map into a set with a pointwise two-sided inverse is an equivalence.
-- No coherence between the two laws is needed: paths in B are unique.
set-equiv : ∀ {a b} {A : Set a} {B : Set b} → IsSet B → {f : A → B}
          → (g : B → A) → ((y : B) → f (g y) ≡ y) → ((x : A) → g (f x) ≡ x)
          → IsEquiv f
set-equiv B-set {f} g s r y =
  (g y , s y) ,
  λ w → fiber-path (sym (ap g (snd w)) ∙ r (fst w)) (B-set _ _ _ _)

private
  pair-eta : ∀ {a b} {A : Set a} {B : Set b} {u w : A × B} (p : u ≡ w)
           → p ≡ pair-path (ap fst p) (ap snd p)
  pair-eta refl = refl

×-set : ∀ {a b} {A : Set a} {B : Set b} → IsSet A → IsSet B → IsSet (A × B)
×-set A-set B-set u w p q =
  pair-eta p
  ∙ ap (λ r → pair-path r (ap snd p)) (A-set _ _ (ap fst p) (ap fst q))
  ∙ ap (pair-path (ap fst q)) (B-set _ _ (ap snd p) (ap snd q))
  ∙ sym (pair-eta q)

------------------------------------------------------------------------

module _ {@♭ ℓ : Level} where

  -- The canonical comparison of two shape data for the same type.
  module Across {@♭ X : Set ℓ} (@♭ s t : ShapeData X) where

    across : ʃ s → ʃ t
    across = rec s (ʃ t) (ʃ-set t) (ʃ-discrete t) (η t)

    across-η : (x : X) → across (η s x) ≡ η t x
    across-η = rec-η s (ʃ t) (ʃ-set t) (ʃ-discrete t) (η t)

  module Choice {@♭ X : Set ℓ} (@♭ s t : ShapeData X) where

    open Across s t public renaming (across to forward; across-η to forward-η)
    open Across t s public renaming (across to backward; across-η to backward-η)

    backward-forward : (z : ʃ s) → backward (forward z) ≡ z
    backward-forward = unique s (ʃ s) (ʃ-set s) (ʃ-discrete s)
      (λ z → backward (forward z)) (λ z → z)
      (λ x → ap backward (forward-η x) ∙ backward-η x)

    forward-backward : (z : ʃ t) → forward (backward z) ≡ z
    forward-backward = unique t (ʃ t) (ʃ-set t) (ʃ-discrete t)
      (λ z → forward (backward z)) (λ z → z)
      (λ x → ap forward (backward-η x) ∙ forward-η x)

    forward-is-equiv : IsEquiv forward
    forward-is-equiv = set-equiv (ʃ-set t) backward forward-backward backward-forward

  -- Shape data pass along a crisp equivalence of the source types, given by
  -- two crisp maps and two pointwise laws.
  module Along {@♭ X X′ : Set ℓ}
    (@♭ i : X′ → X) (@♭ j : X → X′)
    (@♭ i-j : (x : X) → i (j x) ≡ x) (@♭ j-i : (x′ : X′) → j (i x′) ≡ x′)
    (@♭ s : ShapeData X′) where

    along : ShapeData X
    along = shape-data (ʃ s) (ʃ-set s) (ʃ-discrete s) (λ x → η s (j x))
      (λ D D-set D-discrete f → rec s D D-set D-discrete (λ x′ → f (i x′)))
      (λ D D-set D-discrete f x →
          rec-η s D D-set D-discrete (λ x′ → f (i x′)) (j x) ∙ ap f (i-j x))
      (λ D D-set D-discrete g g′ e →
          unique s D D-set D-discrete g g′
            (λ x′ → ap (λ y → g (η s y)) (sym (j-i x′))
                  ∙ e (i x′)
                  ∙ ap (λ y → g′ (η s y)) (j-i x′)))

  -- The Nullstellensatz does not depend on the choice.
  transport-nullstellensatz : {@♭ X : Set ℓ} (@♭ s t : ShapeData X)
                            → Nullstellensatz s → Nullstellensatz t
  transport-nullstellensatz s t n z P P-prop k =
    n (backward z) P P-prop (λ w → k
      ( fst w
      , ( sym (forward-η (counit (fst w)))
        ∙ ap forward (snd w)
        ∙ forward-backward z ) ))
    where open Choice s t

  -- The product comparison commutes with the canonical comparisons.
  module Natural {@♭ X Y : Set ℓ}
    (@♭ sX tX : ShapeData X) (@♭ sY tY : ShapeData Y)
    (@♭ sXY tXY : ShapeData (X × Y)) where

    private
      module AX = Across sX tX
      module AY = Across sY tY
      module AXY = Across sXY tXY

    first-natural : (z : ʃ sXY)
                  → first tX tY tXY (AXY.across z) ≡ AX.across (first sX sY sXY z)
    first-natural = unique sXY (ʃ tX) (ʃ-set tX) (ʃ-discrete tX)
      (λ z → first tX tY tXY (AXY.across z))
      (λ z → AX.across (first sX sY sXY z))
      (λ p → ap (first tX tY tXY) (AXY.across-η p)
           ∙ rec-η tXY (ʃ tX) (ʃ-set tX) (ʃ-discrete tX) (λ q → η tX (fst q)) p
           ∙ sym ( ap AX.across
                     (rec-η sXY (ʃ sX) (ʃ-set sX) (ʃ-discrete sX)
                        (λ q → η sX (fst q)) p)
                 ∙ AX.across-η (fst p) ))

    second-natural : (z : ʃ sXY)
                   → second tX tY tXY (AXY.across z) ≡ AY.across (second sX sY sXY z)
    second-natural = unique sXY (ʃ tY) (ʃ-set tY) (ʃ-discrete tY)
      (λ z → second tX tY tXY (AXY.across z))
      (λ z → AY.across (second sX sY sXY z))
      (λ p → ap (second tX tY tXY) (AXY.across-η p)
           ∙ rec-η tXY (ʃ tY) (ʃ-set tY) (ʃ-discrete tY) (λ q → η tY (snd q)) p
           ∙ sym ( ap AY.across
                     (rec-η sXY (ʃ sY) (ʃ-set sY) (ʃ-discrete sY)
                        (λ q → η sY (snd q)) p)
                 ∙ AY.across-η (snd p) ))

    compare-natural : (z : ʃ sXY)
      → compare tX tY tXY (AXY.across z)
        ≡ (AX.across (first sX sY sXY z) , AY.across (second sX sY sXY z))
    compare-natural z = pair-path (first-natural z) (second-natural z)

  -- Product preservation does not depend on the three choices.
  module ProductChoice {@♭ X Y : Set ℓ}
    (@♭ sX tX : ShapeData X) (@♭ sY tY : ShapeData Y)
    (@♭ sXY tXY : ShapeData (X × Y))
    (pp : PreservesProduct sX sY sXY) where

    private
      module CX = Choice sX tX
      module CY = Choice sY tY
      module CXY = Choice sXY tXY
      module There = Natural sX tX sY tY sXY tXY
      module Back = Natural tX sX tY sY tXY sXY

      inv : ʃ tX × ʃ tY → ʃ tXY
      inv w = CXY.forward (inverse pp (CX.backward (fst w) , CY.backward (snd w)))

      sec : (w : ʃ tX × ʃ tY) → compare tX tY tXY (inv w) ≡ w
      sec w =
        There.compare-natural v
        ∙ pair-path
            (ap CX.forward (ap fst (section pp u)) ∙ CX.forward-backward (fst w))
            (ap CY.forward (ap snd (section pp u)) ∙ CY.forward-backward (snd w))
        where
        u = CX.backward (fst w) , CY.backward (snd w)
        v = inverse pp u

      ret : (z : ʃ tXY) → inv (compare tX tY tXY z) ≡ z
      ret z =
        ap (λ u → CXY.forward (inverse pp u)) (sym (Back.compare-natural z))
        ∙ ap CXY.forward (retraction pp (CXY.backward z))
        ∙ CXY.forward-backward z

    transport-product : PreservesProduct tX tY tXY
    transport-product = set-equiv (×-set (ʃ-set tX) (ʃ-set tY)) inv sec ret
