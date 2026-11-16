{-# OPTIONS --cohesion --without-K --flat-split #-}

-- From a relative reflection to terminal shape data of the total space.
-- Postulate-free. Claude (Fable), 13 November 2026; fable-impl-02;
-- HANDOFF-04 item (d), GENERIC-THEOREM-ROADMAP-AUDIT-01 gate G2 (first half).
--
-- Let K be a whole-context reflection of a family A over a closed discrete
-- base Γ, with total space T, projection p and unit u : Σ Γ A → T.
--
--   TotalExistence K     for ANY discrete Γ, also a higher one: T receives
--                        every crisp map from Σ Γ A to a discrete set D, with
--                        its computation rule. The test target is
--                        Γ × D → Γ; a map over Γ into it is a map into D.
--                        Uses K only.
--   TotalData fe Γ-set K for a SET Γ: T is a set, and (T, u) is terminal
--                        shape data of the closed type Σ Γ A. Uniqueness
--                        uses function extensionality at the level of K.
--
-- The unit of the shape data IS the unit of K, and its carrier IS the total
-- space of K: nothing is identified up to an unnamed equivalence. For a
-- higher Γ the total space is not a set and is not the terminal shape; the
-- terminal shape is then its set truncation (RELATIVE0-HIGHER-BASE-
-- RESEARCH-02 §3), which needs truncations this tree does not have.
--
-- ClosedBridge is the case Γ = CrispUnitAt ℓ, composed with the passage
-- from Σ over the one-point context to the type itself.
module TotalBridge where

open import Foundations
import RelativeSliceShape as R
open R using (RelativeShapeOver; MapOver; over-map; function; triangle)
open import PullbackSetFibers using (transport; retract-set; fiber-fst-set)
open import NativeSharp using (box-crisp-path)
open import ShapeChoice using (FunExtAt)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalPrecohesion

------------------------------------------------------------------------
-- A Σ of sets over a set is a set.

private
  Σ-path : ∀ {a b} {A : Set a} {B : A → Set b} {u w : Σ A B}
         → (p : fst u ≡ fst w) → transport B p (snd u) ≡ snd w → u ≡ w
  Σ-path {u = x , y} refl refl = refl

  fibre-part : ∀ {a b} {A : Set a} {B : A → Set b} {u w : Σ A B} (r : u ≡ w)
         → transport B (ap fst r) (snd u) ≡ snd w
  fibre-part refl = refl

  Σ-eta : ∀ {a b} {A : Set a} {B : A → Set b} {u w : Σ A B} (r : u ≡ w)
        → r ≡ Σ-path (ap fst r) (fibre-part r)
  Σ-eta refl = refl

  Σ-path-cong : ∀ {a b} {A : Set a} {B : A → Set b} {u w : Σ A B}
              → IsSet (B (fst w))
              → {p p′ : fst u ≡ fst w} → p ≡ p′
              → (q : transport B p (snd u) ≡ snd w)
              → (q′ : transport B p′ (snd u) ≡ snd w)
              → Σ-path p q ≡ Σ-path p′ q′
  Σ-path-cong {u = u} {w} B-set {p} refl q q′ =
    ap (Σ-path p) (B-set _ _ q q′)

Σ-set : ∀ {a b} {A : Set a} {B : A → Set b}
      → IsSet A → ((x : A) → IsSet (B x)) → IsSet (Σ A B)
Σ-set A-set B-set u w r r′ =
  Σ-eta r
  ∙ Σ-path-cong (B-set (fst w)) (A-set _ _ (ap fst r) (ap fst r′)) (fibre-part r) (fibre-part r′)
  ∙ sym (Σ-eta r′)

------------------------------------------------------------------------

module _ {@♭ ℓ : Level} where

  module TotalExistence
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
    (@♭ K : RelativeShapeOver Γ dΓ A) where

    T : Set ℓ
    T = R.Output.Total K

    p : T → Γ
    p = R.Output.projection K

    u : Σ Γ A → T
    u = R.Output.unit K

    uo : (a : Σ Γ A) → p (u a) ≡ fst a
    uo = R.Output.unit-over K

    -- A discrete set D as the constant target  Γ × D → Γ.
    module Target (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

      E : Set ℓ
      E = Σ Γ (λ _ → D)

      E-discrete : Discrete E
      E-discrete = SigmaDiscrete.discrete dΓ (λ _ → D-discrete)

      E-set-fibers : R.SetFibers (fst {B = λ (_ : Γ) → D})
      E-set-fibers γ = fiber-fst-set γ D-set

      over : (Σ Γ A → D) → MapOver (fst {B = A}) (fst {B = λ (_ : Γ) → D})
      over f = over-map (λ a → fst a , f a) (λ _ → refl)

      rec₀ : (@♭ f : Σ Γ A → D) → T → D
      rec₀ f z =
        snd (function (R.Output.factor K E E-discrete fst E-set-fibers (over f)) z)

      rec₀-η : (@♭ f : Σ Γ A → D) (a : Σ Γ A) → rec₀ f (u a) ≡ f a
      rec₀-η f a = ap snd
        (R.Output.factor-on-unit K E E-discrete fst E-set-fibers (over f) a)

  module TotalData
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
    {@♭ A : Γ → Set ℓ} (@♭ K : RelativeShapeOver Γ dΓ A) where

    open TotalExistence K

    -- Over a set, a map with set fibres has a set as total space.
    T-set : IsSet T
    T-set = retract-set {B = Σ Γ (R.Output.family K)}
      (λ z → p z , (z , refl)) (λ w → fst (snd w)) (λ _ → refl)
      (Σ-set Γ-set (R.Output.family-set K))

    module Uniqueness (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

      open Target D D-set D-discrete

      private
        pre : MapOver p (fst {B = λ (_ : Γ) → D}) → MapOver (fst {B = A}) fst
        pre = R.precomposeOver Γ A T p u uo E fst

        -- A map into D is a map over Γ into Γ × D, with a trivial triangle.
        lift : (T → D) → MapOver p (fst {B = λ (_ : Γ) → D})
        lift g = over-map (λ z → p z , g z) (λ _ → refl)

        U = R.Output.universal K E E-discrete fst E-set-fibers

        same : (@♭ g g′ : T → D) (@♭ e : (a : Σ Γ A) → g (u a) ≡ g′ (u a))
             → pre (lift g) ≡ pre (lift g′)
        same g g′ e =
          ap (λ (h : Σ Γ A → D) → over-map (λ a → p (u a) , h a) (λ a → refl ∙ uo a))
             (fe e)

        boxed : (@♭ g g′ : T → D) (@♭ e : (a : Σ Γ A) → g (u a) ≡ g′ (u a))
              → box (lift g) ≡ box (lift g′)
        boxed g g′ e = sym (retraction U (box (lift g)))
                     ∙ ap (inverse U) (box-crisp-path (same g g′ e))
                     ∙ retraction U (box (lift g′))

      unique₀ : (@♭ g g′ : T → D) (@♭ e : (a : Σ Γ A) → g (u a) ≡ g′ (u a))
              → (z : T) → g z ≡ g′ z
      unique₀ g g′ e z = ap (λ w → snd (function (counit w) z)) (boxed g g′ e)

    -- Terminal shape data of the total source, with the unit of K.
    total-data : ShapeData (Σ Γ A)
    total-data = shape-data T T-set (R.Output.total-discrete K) u
      (λ D D-set D-discrete f → Target.rec₀ D D-set D-discrete f)
      (λ D D-set D-discrete f → Target.rec₀-η D D-set D-discrete f)
      (λ D D-set D-discrete g g′ e → Uniqueness.unique₀ D D-set D-discrete g g′ e)
