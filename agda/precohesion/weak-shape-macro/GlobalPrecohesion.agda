{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Closed (global) precohesion data as HYPOTHESES. Nothing is postulated.
-- Claude (Fable), 12 November 2026; fable-impl-01. Read FABLE-REVIEW-01.txt,
-- sections 2 and 3, for the semantics and for what is NOT claimed.
--
-- The whole-context macro gives, for a type in a crisp context, one relative
-- reflection with the universal property of that context only. The global
-- axioms of precohesion are of another kind: they speak about the terminal
-- reflections of closed types.
--
--   ShapeData X           terminal-style reflection of X into discrete sets
--   Nullstellensatz s     points-to-pieces  ♭ X → ʃ X  is surjective
--   PreservesProduct      the comparison  ʃ (X × Y) → ʃ X × ʃ Y  is invertible
--   Continuous            κ : ʃ (W → X) → (W → ʃ X)  is invertible
--   EpiC, MonoC           the two halves of continuity
--
-- Every statement here takes its shape data as crisp arguments. A theorem
-- module should take them as crisp module parameters and must not call
-- `shape` on its own parameters: a hypothesis  (@♭ s : ShapeData X)  on a
-- crisp variable X is reflection data that is stable under change of the
-- crisp stage, which a closed instance has (stages are products), and which
-- a capture formed over a universe variable does not have in a model without
-- local connectedness.
--
-- The link to the macro is the statement type ClosedBridge at the end: a
-- closed payload gives ShapeData. ClosedBridge.agda proves it from function
-- extensionality; GlobalPrecohesionExamples.agda runs the whole path.
module GlobalPrecohesion where

open import Foundations
open import DiscretePullback using (crisp-lift)
open import CaptureContext
  using (CrispUnitAt; end-at; unit-at-discrete; unpack-unit-at; Raise)
open import RelativeSliceShape using (RelativeShapeOver)

private
  transport : ∀ {a b} {A : Set a} (P : A → Set b)
            → {x y : A} → x ≡ y → P x → P y
  transport P refl u = u

------------------------------------------------------------------------
-- 1. Shape data: a discrete set S with a map η : X → S, initial among crisp
--    maps from X to discrete sets. Existence and uniqueness are stated for
--    crisp maps, pointwise, so that no function extensionality is needed to
--    use them. Crisp quantification makes both valid at every crisp stage.

module _ {@♭ ℓ : Level} where

  Recursor : (@♭ X S : Set ℓ) (@♭ η : X → S) → Set (lsuc ℓ)
  Recursor X S η =
    (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → (@♭ f : X → D) → S → D

  Computes : (@♭ X S : Set ℓ) (@♭ η : X → S) (@♭ rec : Recursor X S η)
           → Set (lsuc ℓ)
  Computes X S η rec =
    (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → (@♭ f : X → D) (x : X) → rec D D-set D-discrete f (η x) ≡ f x

  Unique : (@♭ X S : Set ℓ) (@♭ η : X → S) → Set (lsuc ℓ)
  Unique X S η =
    (@♭ D : Set ℓ) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → (@♭ g g′ : S → D) (@♭ e : (x : X) → g (η x) ≡ g′ (η x))
    → (z : S) → g z ≡ g′ z

  -- Crisp constructor fields, as in RelativeSliceShape: Agda has no crisp
  -- record fields.
  data ShapeData (@♭ X : Set ℓ) : Set (lsuc ℓ) where
    shape-data : (@♭ S : Set ℓ)
               → (@♭ S-set : IsSet S)
               → (@♭ S-discrete : Discrete S)
               → (@♭ η : X → S)
               → (@♭ rec : Recursor X S η)
               → (@♭ rec-η : Computes X S η rec)
               → (@♭ unique : Unique X S η)
               → ShapeData X

  module _ {@♭ X : Set ℓ} where

    ʃ : (@♭ s : ShapeData X) → Set ℓ
    ʃ (shape-data S _ _ _ _ _ _) = S

    ʃ-set : (@♭ s : ShapeData X) → IsSet (ʃ s)
    ʃ-set (shape-data _ S-set _ _ _ _ _) = S-set

    ʃ-discrete : (@♭ s : ShapeData X) → Discrete (ʃ s)
    ʃ-discrete (shape-data _ _ S-discrete _ _ _ _) = S-discrete

    η : (@♭ s : ShapeData X) → X → ʃ s
    η (shape-data _ _ _ η₀ _ _ _) = η₀

    rec : (@♭ s : ShapeData X) → Recursor X (ʃ s) (η s)
    rec (shape-data _ _ _ _ rec₀ _ _) = rec₀

    rec-η : (@♭ s : ShapeData X) → Computes X (ʃ s) (η s) (rec s)
    rec-η (shape-data _ _ _ _ _ rec-η₀ _) = rec-η₀

    unique : (@♭ s : ShapeData X) → Unique X (ʃ s) (η s)
    unique (shape-data _ _ _ _ _ _ unique₀) = unique₀

------------------------------------------------------------------------
-- 2. Nullstellensatz. `Merely A` says that every proposition of the same
--    universe which follows from A holds; it needs no truncation operation
--    to be stated. It lives one universe up and eliminates into propositions
--    of level ℓ only. Its relation to a propositional truncation is a
--    theorem with hypotheses, not a definition: given a SUPPLIED truncation
--    of level ℓ there are maps both ways without function extensionality,
--    and `Merely A` is itself a proposition under the function
--    extensionality instances listed in GlobalPropositions (fable-impl-03;
--    UNIVERSE-SAFETY-M2-AUDIT-01.txt section 5).

  Merely : Set ℓ → Set (lsuc ℓ)
  Merely A = (P : Set ℓ) → IsProp P → (A → P) → P

  module _ {@♭ X : Set ℓ} where

    points-to-pieces : (@♭ s : ShapeData X) → ♭ X → ʃ s
    points-to-pieces s u = η s (counit u)

    Nullstellensatz : (@♭ s : ShapeData X) → Set (lsuc ℓ)
    Nullstellensatz s = (z : ʃ s) → Merely (Fiber (points-to-pieces s) z)

------------------------------------------------------------------------
-- 3. Binary products. The three shape data are independent hypotheses:
--    nothing relates the shape of X × Y to the shapes of X and Y until
--    PreservesProduct is assumed.

  module _ {@♭ X Y : Set ℓ}
    (@♭ sX : ShapeData X) (@♭ sY : ShapeData Y) (@♭ sXY : ShapeData (X × Y))
    where

    first : ʃ sXY → ʃ sX
    first = rec sXY (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ p → η sX (fst p))

    second : ʃ sXY → ʃ sY
    second = rec sXY (ʃ sY) (ʃ-set sY) (ʃ-discrete sY) (λ p → η sY (snd p))

    compare : ʃ sXY → ʃ sX × ʃ sY
    compare z = first z , second z

    compare-η : (x : X) (y : Y) → compare (η sXY (x , y)) ≡ (η sX x , η sY y)
    compare-η x y = pair-path
      (rec-η sXY (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ p → η sX (fst p)) (x , y))
      (rec-η sXY (ʃ sY) (ʃ-set sY) (ʃ-discrete sY) (λ p → η sY (snd p)) (x , y))

    PreservesProduct : Set ℓ
    PreservesProduct = IsEquiv compare

    -- A first consumer of the two axioms together: with product
    -- preservation, the Nullstellensatz passes from the factors to the
    -- product. (Used for the object  X × Δ2  and its relatives.)
    product-nullstellensatz : PreservesProduct
                            → Nullstellensatz sX → Nullstellensatz sY
                            → Nullstellensatz sXY
    product-nullstellensatz pp nX nY z P P-prop k =
      nX (first z) P P-prop (λ a →
      nY (second z) P P-prop (λ b →
      k (found (fst a) (fst b) (snd a) (snd b))))
      where
      found : (u : ♭ X) (v : ♭ Y)
            → points-to-pieces sX u ≡ first z
            → points-to-pieces sY v ≡ second z
            → Fiber (points-to-pieces sXY) z
      found (box x) (box y) e e′ =
        box (x , y) ,
        ( sym (retraction pp (η sXY (x , y)))
        ∙ ap (inverse pp) (compare-η x y ∙ pair-path e e′)
        ∙ retraction pp z )

------------------------------------------------------------------------
-- 4. Induction on a discrete type from its crisp points, with its
--    computation rule at a crisp point. (DiscretePullback.discrete-ind is
--    the same operation; its rule is proved here.)

  private
    on-flat : ∀ {b} {@♭ A : Set ℓ} (P : A → Set b)
            → ((@♭ x : A) → P x) → (u : ♭ A) → P (counit u)
    on-flat P k (box x) = k x

  discrete-elim : ∀ {b} {@♭ A : Set ℓ} (@♭ dA : Discrete A) (P : A → Set b)
                → ((@♭ x : A) → P x) → (x : A) → P x
  discrete-elim dA P k x =
    transport P (section dA x) (on-flat P k (inverse dA x))

  discrete-elim-β : ∀ {b} {@♭ A : Set ℓ} (@♭ dA : Discrete A) (P : A → Set b)
                  → (k : (@♭ x : A) → P x) (@♭ x : A)
                  → discrete-elim dA P k x ≡ k x
  discrete-elim-β {A = A} dA P k x =
    help (inverse dA x) (section dA x) (fst lifted) (snd lifted)
    where
    lifted = crisp-lift (inverse dA x) x (section dA x)

    help : (u : ♭ A) (e : counit u ≡ x) (q : u ≡ box x)
         → ap counit q ≡ e → transport P e (on-flat P k u) ≡ k x
    help .(box x) .refl refl refl = refl

------------------------------------------------------------------------
-- 5. Continuity. W is the exponent: in the paper a discrete SET; the
--    comparison itself needs only discreteness. For a crisp point w,
--    evaluation at w is a crisp map (W → X) → X; a general w is reached
--    by induction on the discrete type W. No product axiom is used.

  module _ {@♭ X W : Set ℓ} (@♭ W-discrete : Discrete W)
    (@♭ sX : ShapeData X) (@♭ sF : ShapeData (W → X)) where

    at-point : (@♭ w : W) → ʃ sF → ʃ sX
    at-point w = rec sF (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ f → η sX (f w))

    κ : ʃ sF → W → ʃ sX
    κ z = discrete-elim W-discrete (λ _ → ʃ sX) (λ w → at-point w z)

    κ-η : (f : W → X) (w : W) → κ (η sF f) w ≡ η sX (f w)
    κ-η f = discrete-elim W-discrete (λ w → κ (η sF f) w ≡ η sX (f w))
      (λ w → discrete-elim-β W-discrete (λ _ → ʃ sX)
               (λ w′ → at-point w′ (η sF f)) w
           ∙ rec-η sF (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ g → η sX (g w)) f)

    Continuous : Set ℓ
    Continuous = IsEquiv κ

    EpiC : Set (lsuc ℓ)
    EpiC = (g : W → ʃ sX) → Merely (Fiber κ g)

    MonoC : Set ℓ
    MonoC = (a b : ʃ sF) → κ a ≡ κ b → a ≡ b

------------------------------------------------------------------------
-- 6. Two facts that need no axiom beyond the shape data: the shape of a
--    discrete set is that set, and the shape of the unit type is
--    contractible (the nullary case of product preservation). Neither uses
--    function extensionality.

  module _ {@♭ D : Set ℓ} (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    (@♭ s : ShapeData D) where

    back : ʃ s → D
    back = rec s D D-set D-discrete (λ d → d)

    back-η : (d : D) → back (η s d) ≡ d
    back-η = rec-η s D D-set D-discrete (λ d → d)

    η-back : (z : ʃ s) → η s (back z) ≡ z
    η-back = unique s (ʃ s) (ʃ-set s) (ʃ-discrete s)
      (λ z → η s (back z)) (λ z → z) (λ d → ap (η s) (back-η d))

shape-of-unit : (@♭ s : ShapeData ⊤) → IsContr (ʃ s)
shape-of-unit s =
  η s tt ,
  unique s (ʃ s) (ʃ-set s) (ʃ-discrete s) (λ _ → η s tt) (λ z → z) (λ _ → refl)

------------------------------------------------------------------------
-- 7. The link to the whole-context macro. For a closed X : Set ℓ the macro
--    declares one constant of type  Closed X. That it yields ShapeData X is
--    proved in ClosedBridge.agda: existence from the constant alone,
--    uniqueness with function extensionality at level ℓ (CrispUnitAt has no
--    eta rule, so maps out of the packed total space are compared pointwise).

Closed : {@♭ ℓ : Level} (@♭ X : Set ℓ) → Set (lsuc ℓ)
Closed {ℓ} X =
  RelativeShapeOver (CrispUnitAt ℓ) unit-at-discrete (unpack-unit-at (Raise ℓ X))

ClosedBridge : (@♭ ℓ : Level) → Set (lsuc ℓ)
ClosedBridge ℓ = (@♭ X : Set ℓ) (@♭ K : Closed X) → ShapeData X
