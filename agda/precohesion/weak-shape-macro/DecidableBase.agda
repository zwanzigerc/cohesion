{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Over a discrete base with decidable equality, a whole-context reflection
-- is fibrewise. Postulate-free: no product axiom, no Nullstellensatz, no
-- continuity. Claude (Fable), 13 November 2026; fable-impl-02; HANDOFF-04
-- item (e), GENERIC-THEOREM-ROADMAP-AUDIT-01 gates G2 and G4.
--
-- Let K be a whole-context reflection of a family A over a closed discrete
-- base Γ with decidable equality (so Γ is a set), and γ₀ a crisp point.
--
--   Fibre.fibre-data : ShapeData (A γ₀)
--
-- with carrier the fibre  family K γ₀  of K and unit  family-unit K γ₀:
-- the fibre of the reflection IS the terminal reflection of the fibre.
--
-- Why this matters. In a module with crisp parameters ranging over discrete
-- types with decidable equality (numbers, finite types, codes), γ₀ is the
-- current point of the packed context and K the constant that `shape`
-- declared there. So a FRESH capture in such an open crisp context yields
-- terminal-style shape data for its source type, at the current point, as
-- data that are stable in the sense of FABLE-REVIEW-01 §2.2. Every
-- hypothesis-parameterised theorem then applies in that context directly.
-- CaptureFibre packages this for a captured shape.
--
-- Semantics: the complemented-subobject case of FABLE-REVIEW-01 Theorem 3.4
-- (with Δ fully faithful). A point of a decidable object is a complemented
-- subobject, Π preserves the resulting coproduct decomposition, and no
-- product law is needed.
--
-- Proof. A crisp map f : A γ₀ → D is extended to the total space by sending
-- everything outside the fibre to a point: the target over Γ has fibre D
-- over γ₀ and a one-point fibre elsewhere (`Pick`), which is where
-- decidability is used. Uniqueness uses function extensionality at the level
-- of K, as in ClosedBridge and TotalBridge.
--
-- What this does NOT give: anything over a base without decidable equality,
-- in particular over a context that contains a type variable.
module DecidableBase where

open import Foundations
import RelativeSliceShape as R
open R using (RelativeShapeOver; MapOver; over-map; function; triangle)
open import PullbackSetFibers using (transport; fiber-fst-set)
open import FlatContext using (fiber-path)
open import NativeSharp using (box-crisp-path)
open import ShapeChoice using (FunExtAt)
open import ShapeElim
  using (module SigmaDiscrete; module FiberDiscrete; raise-set; raise-discrete)
open import CaptureContext
  using (Raise; raise; CrispUnitAt; end-at; CrispΣ; pair; unpack)
open import CapturedShape using (CapturedShape)
import CapturedShape as C
open import GlobalPrecohesion
open import GlobalChoice using (module Along)

------------------------------------------------------------------------
-- Decidability.

-- ⊥, absurd, Dec, yes, no and DecEq are declared in DecidableData since
-- step S3c (after fable-impl-13): the data of a captured diagram bundle
-- store a decision procedure and lie below the capture frontend, which
-- must not import the proofs of this module. They are re-exported here
-- unchanged; there is one definition of each.
open import DecidableData public

-- Hedberg: decidable equality makes a set.
module _ {a} {A : Set a} (dec : DecEq A) where
  private
    collapse : {x y : A} → Dec (x ≡ y) → x ≡ y → x ≡ y
    collapse (yes q) _ = q
    collapse (no n) p = absurd (n p)

    constant : {x y : A} (d : Dec (x ≡ y)) (p q : x ≡ y)
             → collapse d p ≡ collapse d q
    constant (yes _) p q = refl
    constant (no n) p q = absurd (n p)

    cancel : {x y : A} (c : x ≡ y) → sym c ∙ c ≡ refl
    cancel refl = refl

    recover : {x y : A} (p : x ≡ y)
            → p ≡ sym (collapse (dec x x) refl) ∙ collapse (dec x y) p
    recover {x} refl = sym (cancel (collapse (dec x x) refl))

  decidable-set : IsSet A
  decidable-set x y p q =
    recover p
    ∙ ap (λ r → sym (collapse (dec x x) refl) ∙ r) (constant (dec x y) p q)
    ∙ sym (recover q)

-- Packed contexts of decidable types are decidable.
unit-at-dec : {@♭ ℓ : Level} → DecEq (CrispUnitAt ℓ)
unit-at-dec end-at end-at = yes refl

-- One more variable in front of a decidable context, for a context that
-- does not depend on it. (A dependent tail needs injectivity of `pair` over
-- a decidable head; not done here.)
module _ {@♭ a b : Level} {@♭ A : Set a} {@♭ B : Set b}
  (@♭ dA : DecEq A) (@♭ dB : DecEq B) where

  private
    Ctx : Set (a ⊔ b)
    Ctx = CrispΣ A (λ _ → B)

    head : Ctx → A
    head = unpack (λ x _ → x)

    rest : Ctx → B
    rest = unpack (λ _ y → y)

    tails : (@♭ x : A) (@♭ y y′ : B) (@♭ d : Dec (y ≡ y′))
          → Dec (pair {B = λ _ → B} x y ≡ pair x y′)
    tails x y .y (yes refl) = yes refl
    tails x y y′ (no n) = no (λ e → n (ap rest e))

    heads : (@♭ x x′ : A) (@♭ d : Dec (x ≡ x′)) (@♭ y y′ : B)
          → Dec (pair {B = λ _ → B} x y ≡ pair x′ y′)
    heads x .x (yes refl) y y′ = tails x y y′ (dB y y′)
    heads x x′ (no n) y y′ = no (λ e → n (ap head e))

  context-dec : DecEq (CrispΣ A (λ _ → B))
  context-dec (pair x y) (pair x′ y′) = heads x x′ (dA x x′) y y′

------------------------------------------------------------------------
-- The fibre of a reflection over a decidable base.

private
  unit-set : IsSet ⊤
  unit-set tt tt refl refl = refl

  unit-discrete : Discrete ⊤
  unit-discrete tt = (box tt , refl) , λ where (box tt , refl) → refl

module _ {@♭ ℓ : Level} where

  module Fibre
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ dec : DecEq Γ)
    {@♭ A : Γ → Set ℓ} (@♭ K : RelativeShapeOver Γ dΓ A) (@♭ γ₀ : Γ) where

    private
      Γ-set : IsSet Γ
      Γ-set = decidable-set dec

      T : Set ℓ
      T = R.Output.Total K

      p : T → Γ
      p = R.Output.projection K

      u : Σ Γ A → T
      u = R.Output.unit K

      uo : (a : Σ Γ A) → p (u a) ≡ fst a
      uo = R.Output.unit-over K

    S₀ : Set ℓ
    S₀ = R.Output.family K γ₀

    η₀ : A γ₀ → S₀
    η₀ = R.Output.family-unit K γ₀

    S₀-discrete : Discrete S₀
    S₀-discrete = FiberDiscrete.discrete dΓ (R.Output.total-discrete K) p γ₀

    module Target (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

      -- D over γ₀, one point elsewhere.
      Pick : {γ : Γ} → Dec (γ ≡ γ₀) → Set ℓ
      Pick (yes _) = D
      Pick (no _) = Raise ℓ ⊤

      pick-set : {γ : Γ} (d : Dec (γ ≡ γ₀)) → IsSet (Pick d)
      pick-set (yes _) = D-set
      pick-set (no _) = raise-set unit-set

      pick-discrete : {@♭ γ : Γ} (@♭ d : Dec (γ ≡ γ₀)) → Discrete (Pick d)
      pick-discrete (yes _) = D-discrete
      pick-discrete (no _) = raise-discrete unit-discrete

      D̂ : Γ → Set ℓ
      D̂ γ = Pick (dec γ γ₀)

      E : Set ℓ
      E = Σ Γ D̂

      E-discrete : Discrete E
      E-discrete = SigmaDiscrete.discrete dΓ (λ γ → pick-discrete (dec γ γ₀))

      E-set-fibers : R.SetFibers (fst {B = D̂})
      E-set-fibers γ = fiber-fst-set γ (pick-set (dec γ γ₀))

      -- Into the target: f on the fibre over γ₀, the point elsewhere.
      pick-map : (A γ₀ → D) → {γ : Γ} (d : Dec (γ ≡ γ₀)) → A γ → Pick d
      pick-map f (yes e) a = f (transport A e a)
      pick-map f (no _) a = raise tt

      over : (A γ₀ → D) → MapOver (fst {B = A}) (fst {B = D̂})
      over f = over-map (λ a → fst a , pick-map f (dec (fst a) γ₀) (snd a)) (λ _ → refl)

      -- Out of the target, over γ₀.
      extract : {γ : Γ} (d : Dec (γ ≡ γ₀)) → γ ≡ γ₀ → Pick d → D
      extract (yes _) _ x = x
      extract (no n) e _ = absurd (n e)

      out : (w : E) → fst w ≡ γ₀ → D
      out w e = extract (dec (fst w) γ₀) e (snd w)

      out-path : {w w′ : E} (r : w ≡ w′) (e : fst w ≡ γ₀) (e′ : fst w′ ≡ γ₀)
               → out w e ≡ out w′ e′
      out-path {w} refl e e′ = ap (out w) (Γ-set _ _ e e′)

      private
        factored : (@♭ f : A γ₀ → D) → MapOver p (fst {B = D̂})
        factored f = R.Output.factor K E E-discrete fst E-set-fibers (over f)

        diagonal : (f : A γ₀ → D) (d : Dec (γ₀ ≡ γ₀)) (a : A γ₀)
                 → extract d refl (pick-map f d a) ≡ f a
        diagonal f (yes e) a = ap (λ e′ → f (transport A e′ a)) (Γ-set _ _ e refl)
        diagonal f (no n) a = absurd (n refl)

      rec₀ : (@♭ f : A γ₀ → D) → S₀ → D
      rec₀ f z = out (function (factored f) (fst z))
                     (triangle (factored f) (fst z) ∙ snd z)

      rec₀-η : (@♭ f : A γ₀ → D) (a : A γ₀) → rec₀ f (η₀ a) ≡ f a
      rec₀-η f a =
        out-path (R.Output.factor-on-unit K E E-discrete fst E-set-fibers (over f) (γ₀ , a))
                 (triangle (factored f) (u (γ₀ , a)) ∙ uo (γ₀ , a)) refl
        ∙ diagonal f (dec γ₀ γ₀) a

      ------------------------------------------------------------------
      -- Uniqueness.

      private
        -- A map on the fibre, extended to the total space over Γ.
        pickG : (S₀ → D) → (z : T) (d : Dec (p z ≡ γ₀)) → Pick d
        pickG g z (yes e) = g (z , e)
        pickG g z (no _) = raise tt

        lift : (S₀ → D) → MapOver p (fst {B = D̂})
        lift g = over-map (λ z → p z , pickG g z (dec (p z) γ₀)) (λ _ → refl)

        pre : MapOver p (fst {B = D̂}) → MapOver (fst {B = A}) (fst {B = D̂})
        pre = R.precomposeOver Γ A T p u uo E fst

        U = R.Output.universal K E E-discrete fst E-set-fibers

        -- On a unit that lies over γ₀ the two maps agree by hypothesis.
        at-γ₀ : (g g′ : S₀ → D) → ((a : A γ₀) → g (η₀ a) ≡ g′ (η₀ a))
              → (γ : Γ) → γ ≡ γ₀ → (x : A γ) (e₁ : p (u (γ , x)) ≡ γ₀)
              → g (u (γ , x) , e₁) ≡ g′ (u (γ , x) , e₁)
        at-γ₀ g g′ h .γ₀ refl x e₁ =
          ap g same-point ∙ h x ∙ sym (ap g′ same-point)
          where
          same-point : _≡_ {A = S₀} (u (γ₀ , x) , e₁) (η₀ x)
          same-point = fiber-path refl (Γ-set _ _ _ _)

        agree : (g g′ : S₀ → D) → ((a : A γ₀) → g (η₀ a) ≡ g′ (η₀ a))
              → (a : Σ Γ A) (d : Dec (p (u a) ≡ γ₀))
              → pickG g (u a) d ≡ pickG g′ (u a) d
        agree g g′ h a (no _) = refl
        agree g g′ h a (yes e₁) =
          at-γ₀ g g′ h (fst a) (sym (uo a) ∙ e₁) (snd a) e₁

        same : (@♭ g g′ : S₀ → D) (@♭ h : (a : A γ₀) → g (η₀ a) ≡ g′ (η₀ a))
             → pre (lift g) ≡ pre (lift g′)
        same g g′ h =
          ap (λ (k : (a : Σ Γ A) → D̂ (p (u a))) →
                over-map (λ a → p (u a) , k a) (λ a → refl ∙ uo a))
             (fe (λ a → agree g g′ h a (dec (p (u a)) γ₀)))

        boxed : (@♭ g g′ : S₀ → D) (@♭ h : (a : A γ₀) → g (η₀ a) ≡ g′ (η₀ a))
              → box (lift g) ≡ box (lift g′)
        boxed g g′ h = sym (retraction U (box (lift g)))
                     ∙ ap (inverse U) (box-crisp-path (same g g′ h))
                     ∙ retraction U (box (lift g′))

        out-pick : (g : S₀ → D) (z : T) (e : p z ≡ γ₀) (d : Dec (p z ≡ γ₀))
                 → extract d e (pickG g z d) ≡ g (z , e)
        out-pick g z e (yes e₁) = ap (λ e′ → g (z , e′)) (Γ-set _ _ e₁ e)
        out-pick g z e (no n) = absurd (n e)

      unique₀ : (@♭ g g′ : S₀ → D) (@♭ h : (a : A γ₀) → g (η₀ a) ≡ g′ (η₀ a))
              → (s : S₀) → g s ≡ g′ s
      unique₀ g g′ h s =
        sym (out-pick g (fst s) (snd s) (dec (p (fst s)) γ₀))
        ∙ out-path (ap (λ w → function (counit w) (fst s)) (boxed g g′ h)) (snd s) (snd s)
        ∙ out-pick g′ (fst s) (snd s) (dec (p (fst s)) γ₀)

    -- The fibre of K over γ₀, with the unit of K, is terminal shape data
    -- of the fibre A γ₀.
    fibre-data : ShapeData (A γ₀)
    fibre-data = shape-data S₀ (R.Output.family-set K γ₀) S₀-discrete η₀
      (λ D D-set D-discrete f → Target.rec₀ D D-set D-discrete f)
      (λ D D-set D-discrete f → Target.rec₀-η D D-set D-discrete f)
      (λ D D-set D-discrete g g′ h → Target.unique₀ D D-set D-discrete g g′ h)

  -- For a captured shape whose packed context has decidable equality: shape
  -- data of the source type itself, at the current point of the context.
  module CaptureFibre
    (@♭ fe : FunExtAt ℓ) {@♭ A : Set ℓ} (@♭ s : CapturedShape {ℓ = ℓ} A)
    (@♭ dec : DecEq (C.Output.context s)) where

    capture-data : ShapeData A
    capture-data = Along.along
      (C.Output.source-decode s) (C.Output.source-embed s)
      (C.Output.source-section s) (C.Output.source-retraction s)
      (Fibre.fibre-data fe dec (C.Output.whole-context s) (C.Output.point s))
