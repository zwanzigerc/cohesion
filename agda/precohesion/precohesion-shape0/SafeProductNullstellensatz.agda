{-# OPTIONS --safe --without-K --cohesion #-}

-- A consumer of the global axioms at trust level L0: literally --safe.
-- Claude (Fable), 13 November 2026; fable-impl-02, HANDOFF-04 item (f).
--
-- --safe refuses the option pair --without-K --flat-split, and a --safe
-- module cannot import one that is not --safe. A data type with crisp
-- constructor fields (ShapeData, RelativeShapeOver) forces --flat-split on
-- whoever takes it apart. So an L0 theorem takes the PIECES it uses as
-- module parameters, and takes exactly those: here the two sources, three
-- carriers and three units, which are crisp, and the two components of the
-- product comparison with their rules on units, which are ORDINARY
-- parameters (fable-impl-03: the comment of fable-impl-02 called all of
-- them crisp; the signature below is the more general one and is
-- unchanged). It imports Foundations only. No axiom, generated or not, can reach
-- this module; a module that instantiates it from generated shapes is at
-- level L2 and is not this one (weak-shape-macro/SafeConsumerExamples.agda).
--
-- Theorem: if the comparison is an equivalence and the Nullstellensatz holds
-- for X and for Y, it holds for X × Y.
open import Foundations

module SafeProductNullstellensatz
  {@♭ ℓ : Level} (@♭ X Y : Set ℓ)
  (@♭ SX SY SXY : Set ℓ)
  (@♭ ηX : X → SX) (@♭ ηY : Y → SY) (@♭ ηXY : X × Y → SXY)
  (first : SXY → SX) (second : SXY → SY)
  (first-η : (p : X × Y) → first (ηXY p) ≡ ηX (fst p))
  (second-η : (p : X × Y) → second (ηXY p) ≡ ηY (snd p))
  where

-- Elimination into propositions of level ℓ only; the type is one level up.
Merely : Set ℓ → Set (lsuc ℓ)
Merely A = (P : Set ℓ) → IsProp P → (A → P) → P

PointsX : Set (lsuc ℓ)
PointsX = (z : SX) → Merely (Fiber (λ (u : ♭ X) → ηX (counit u)) z)

PointsY : Set (lsuc ℓ)
PointsY = (z : SY) → Merely (Fiber (λ (u : ♭ Y) → ηY (counit u)) z)

PointsXY : Set (lsuc ℓ)
PointsXY = (z : SXY) → Merely (Fiber (λ (u : ♭ (X × Y)) → ηXY (counit u)) z)

compare : SXY → SX × SY
compare z = first z , second z

private
  found : (pp : IsEquiv compare) (z : SXY) (u : ♭ X) (v : ♭ Y)
        → ηX (counit u) ≡ first z → ηY (counit v) ≡ second z
        → Fiber (λ (w : ♭ (X × Y)) → ηXY (counit w)) z
  found pp z (box x) (box y) e e′ =
    box (x , y) ,
    ( sym (retraction pp (ηXY (x , y)))
    ∙ ap (inverse pp) (pair-path (first-η (x , y) ∙ e) (second-η (x , y) ∙ e′))
    ∙ retraction pp z )

product-nullstellensatz : IsEquiv compare → PointsX → PointsY → PointsXY
product-nullstellensatz pp nX nY z P P-prop k =
  nX (first z) P P-prop (λ a →
  nY (second z) P P-prop (λ b →
  k (found pp z (fst a) (fst b) (snd a) (snd b))))
