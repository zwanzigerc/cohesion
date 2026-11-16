{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Ordinary parameters of DISCRETE type, and the product-stage law.
-- Postulate-free; no function extensionality; no product axiom.
-- Claude (Fable), 13 November 2026; fable-impl-02, HANDOFF-04 item (e).
--
-- The universal property of a shape speaks about crisp maps. A map that
-- depends on an ordinary variable j is not crisp. If j ranges over a crisp
-- DISCRETE type J, it is reached all the same: do the crisp construction at
-- each crisp point of J and extend by induction on the discrete type J.
--
--   Parameter          rec with a parameter j : J, for terminal shape data
--   CaptureParameter   the same for a whole-context capture, at its exact
--                      captured context (ShapeElim.Elim) plus j
--   ProductStage       ʃ (J × X) ≃ J × ʃ X  for a crisp discrete SET J,
--                      compatibly with the units
--
-- ProductStage is the native form of the law  Π(ΔJ × X) ≅ J × ΠX  that the
-- semantics of every closed shape axiom needs at each crisp stage
-- (FABLE-REVIEW-01 §2.1). It is a theorem of the shape data; the product
-- axiom of the basic theory is not used.
--
-- Levels: J, the targets and the shapes are at the one crisp level ℓ of the
-- shape data (for a capture: the level of its captured context). A parameter
-- of ARBITRARY ordinary type is not covered and cannot be without a product
-- instance: that would make discrete sets an exponential ideal.
module DiscreteParameters where

open import Foundations
open import GlobalPrecohesion
open import GlobalChoice using (set-equiv; ×-set)
open import CapturedShape using (CapturedShape)
import CapturedShape as C
open import ShapeElim using (module SigmaDiscrete; module Elim)

module _ {@♭ ℓ : Level} where

  module Parameter
    {@♭ X : Set ℓ} (@♭ s : ShapeData X)
    {@♭ J : Set ℓ} (@♭ J-discrete : Discrete J)
    (@♭ D : J → Set ℓ)
    (@♭ D-set : (j : J) → IsSet (D j))
    (@♭ D-discrete : (@♭ j : J) → Discrete (D j))
    (@♭ f : (j : J) → X → D j) where

    rec-at : (@♭ j : J) → ʃ s → D j
    rec-at j = rec s (D j) (D-set j) (D-discrete j) (f j)

    rec-param : (j : J) → ʃ s → D j
    rec-param = discrete-elim J-discrete (λ j → ʃ s → D j) rec-at

    rec-param-η : (j : J) (x : X) → rec-param j (η s x) ≡ f j x
    rec-param-η = discrete-elim J-discrete
      (λ j → (x : X) → rec-param j (η s x) ≡ f j x)
      (λ j x → ap (λ h → h (η s x))
                  (discrete-elim-β J-discrete (λ j′ → ʃ s → D j′) rec-at j)
             ∙ rec-η s (D j) (D-set j) (D-discrete j) (f j) x)

  module CaptureParameter
    {@♭ a : Level} {@♭ A : Set a} (@♭ s : CapturedShape {ℓ = ℓ} A)
    {@♭ J : Set ℓ} (@♭ J-discrete : Discrete J)
    (@♭ D̂ : J → C.Output.context s → Set ℓ)
    (@♭ D̂-set : (j : J) (γ : C.Output.context s) → IsSet (D̂ j γ))
    (@♭ D̂-discrete : (@♭ j : J) (@♭ γ : C.Output.context s) → Discrete (D̂ j γ))
    (@♭ f̂ : (j : J) (γ : C.Output.context s) → C.Output.family s γ → D̂ j γ)
    where

    private
      Target : J → Set ℓ
      Target j = C.Output.carrier s → D̂ j (C.Output.point s)

    rec-at : (@♭ j : J) → Target j
    rec-at j = Elim.rec s (D̂ j) (D̂-set j) (D̂-discrete j) (f̂ j)

    rec-param : (j : J) → Target j
    rec-param = discrete-elim J-discrete Target rec-at

    rec-param-β : (j : J) (x : A)
                → rec-param j (C.Output.unit s x)
                  ≡ f̂ j (C.Output.point s) (C.Output.source-embed s x)
    rec-param-β = discrete-elim J-discrete
      (λ j → (x : A) → rec-param j (C.Output.unit s x)
                       ≡ f̂ j (C.Output.point s) (C.Output.source-embed s x))
      (λ j x → ap (λ h → h (C.Output.unit s x))
                  (discrete-elim-β J-discrete Target rec-at j)
             ∙ Elim.rec-β s (D̂ j) (D̂-set j) (D̂-discrete j) (f̂ j) x)

  module ProductStage
    {@♭ X J : Set ℓ} (@♭ J-set : IsSet J) (@♭ J-discrete : Discrete J)
    (@♭ sX : ShapeData X) (@♭ sJX : ShapeData (J × X)) where

    target-set : IsSet (J × ʃ sX)
    target-set = ×-set J-set (ʃ-set sX)

    target-discrete : Discrete (J × ʃ sX)
    target-discrete = SigmaDiscrete.discrete J-discrete (λ _ → ʃ-discrete sX)

    forward : ʃ sJX → J × ʃ sX
    forward = rec sJX (J × ʃ sX) target-set target-discrete
      (λ p → fst p , η sX (snd p))

    forward-η : (j : J) (x : X) → forward (η sJX (j , x)) ≡ (j , η sX x)
    forward-η j x = rec-η sJX (J × ʃ sX) target-set target-discrete
      (λ p → fst p , η sX (snd p)) (j , x)

    private
      module P = Parameter sX J-discrete (λ _ → ʃ sJX) (λ _ → ʃ-set sJX)
                   (λ _ → ʃ-discrete sJX) (λ j x → η sJX (j , x))

    backward : J × ʃ sX → ʃ sJX
    backward w = P.rec-param (fst w) (snd w)

    backward-η : (j : J) (x : X) → backward (j , η sX x) ≡ η sJX (j , x)
    backward-η = P.rec-param-η

    backward-forward : (z : ʃ sJX) → backward (forward z) ≡ z
    backward-forward = unique sJX (ʃ sJX) (ʃ-set sJX) (ʃ-discrete sJX)
      (λ z → backward (forward z)) (λ z → z)
      (λ p → ap backward (forward-η (fst p) (snd p)) ∙ backward-η (fst p) (snd p))

    private
      at : (j : J) (z : ʃ sX) → forward (backward (j , z)) ≡ (j , z)
      at = discrete-elim J-discrete
        (λ j → (z : ʃ sX) → forward (backward (j , z)) ≡ (j , z))
        (λ j → unique sX (J × ʃ sX) target-set target-discrete
                 (λ z → forward (backward (j , z))) (λ z → j , z)
                 (λ x → ap forward (backward-η j x) ∙ forward-η j x))

    forward-backward : (w : J × ʃ sX) → forward (backward w) ≡ w
    forward-backward w = at (fst w) (snd w)

    -- ʃ (J × X) ≃ J × ʃ X, by the canonical map, which preserves units.
    stage-equiv : IsEquiv forward
    stage-equiv = set-equiv target-set backward forward-backward backward-forward
