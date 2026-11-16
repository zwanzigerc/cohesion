{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The universal property of a SMALL carrier and unit against LARGE discrete
-- sets, in canonical form, as a HYPOTHESIS. Claude (Fable), 13 November
-- 2026; fable-impl-03. Nothing is postulated in this module and it declares
-- nothing: the closed declaration schema is LargeTargetDeclare.
-- HANDOFF-06 item 5, CLASSIFIER-LARGE-UP-SCHEMA-01.txt,
-- CLASSIFIER-LARGE-UP-M1-AUDIT-02.txt, UNIVERSE-SAFETY-M2-AUDIT-01.txt.
--
-- For crisp X, S : Set a and a crisp unit η₀ : X → S, and a level L,
--
--   LargeTerminalUP L X S η₀ =
--     (@♭ D : Set (a ⊔ L)) → IsSet D → Discrete D
--     → IsEquiv (flat-map (λ g → g ∘ η₀) : ♭ (S → D) → ♭ (X → D))
--
-- The statement is about the actual precomposition map for the actual unit.
-- It mentions no function extensionality, no shape datum and no recursor;
-- the ceiling of the targets is a ⊔ L, and S stays in Set a.
--
-- Contents, with the extensionality each part uses (all of it as a crisp
-- hypothesis  FunExt₂ a (a ⊔ L) : functions from Set a into Set (a ⊔ L)):
--
--   At                recursor and its rule on units           none
--   At.recLarge-unique  pointwise uniqueness                   FunExt₂ a (a ⊔ L)
--   to-pointwise      the pointwise form of fable-impl-02
--                     (LargeElimination)                       FunExt₂ a (a ⊔ L)
--   from-pointwise    and back                                 FunExt₂ a (a ⊔ L)
--   Restrict          a smaller ceiling, same carrier and unit none
--   Old               the same-level recursor agrees with the
--                     one of a given shape datum               none
--   Transfer          along a unit-preserving equivalence      FunExt₂ a (a ⊔ L)
--   RaisedData        shape data for Raise L X with carrier
--                     Raise L S                                FunExt₂ a (a ⊔ L)
--   MapShape          the action on a map into a larger type   none
--   SharpComposite    naturality of the coaugmentation of
--                     T = shape ∘ ♯                            none
--
-- There is no operation from a smaller ceiling to a larger one, and none
-- that makes a certificate from a shape datum at a larger ceiling than its
-- own level. Merely and the Nullstellensatz are not mentioned: this
-- hypothesis does not enlarge their elimination.
module LargeTarget where

open import Foundations
open import CaptureContext using (Raise; raise; lower; raise-lower)
open import NativeSharp using (box-crisp-path; ♯; sharp-unit; sharp-map; sharp-map-unit)
open import Adjointify using (quasi-inverse)
open import GlobalPrecohesion
  using (ShapeData; shape-data; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; unique)
open import GlobalPropositions using (FunExt₂)
open import LargeElimination
  using (raise-set; raise-discrete; LargeElimination; large;
         large-rec; large-rec-η; large-unique)

------------------------------------------------------------------------
-- 1. The certificate.

module _ {@♭ a : Level} (@♭ L : Level) (@♭ X S : Set a) (@♭ η₀ : X → S) where

  precompose : (@♭ D : Set (a ⊔ L)) → ♭ (S → D) → ♭ (X → D)
  precompose D = flat-map (λ g x → g (η₀ x))

  LargeTerminalUP : Set (lsuc (a ⊔ L))
  LargeTerminalUP =
    (@♭ D : Set (a ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
    → IsEquiv (precompose D)

-- For a shape datum: the same carrier and unit. This makes no new shape.
LargeOn : {@♭ a : Level} (@♭ L : Level) {@♭ X : Set a}
        → (@♭ s : ShapeData X) → Set (lsuc (a ⊔ L))
LargeOn L {X = X} s = LargeTerminalUP L X (ʃ s) (η s)

private
  -- A crisp element of ♭ A is the box of its counit.
  rebox : {@♭ a : Level} {@♭ A : Set a} (@♭ w : ♭ A) → box (counit w) ≡ w
  rebox (box x) = refl

------------------------------------------------------------------------
-- 2. Recursor, its rule on units, and pointwise uniqueness.

module At {@♭ a : Level} (@♭ L : Level) {@♭ X S : Set a} {@♭ η₀ : X → S}
  (@♭ c : LargeTerminalUP L X S η₀)
  (@♭ D : Set (a ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

  private
    E : IsEquiv (precompose L X S η₀ D)
    E = c D D-set D-discrete

  recLarge : (@♭ f : X → D) → S → D
  recLarge f = counit (inverse E (box f))

  private
    on-units : (@♭ f : X → D) → (λ x → recLarge f (η₀ x)) ≡ f
    on-units f =
      sym (flat-map-counit (λ g x → g (η₀ x)) (inverse E (box f)))
      ∙ ap counit (section E (box f))

  -- No function extensionality: happly is the direction that needs none.
  recLarge-η : (@♭ f : X → D) (x : X) → recLarge f (η₀ x) ≡ f x
  recLarge-η f x = happly (on-units f) x

  private
    boxed : (@♭ fe : FunExt₂ a (a ⊔ L))
          → (@♭ g g′ : S → D) (@♭ e : (x : X) → g (η₀ x) ≡ g′ (η₀ x))
          → box g ≡ box g′
    boxed fe g g′ e = sym (retraction E (box g))
                    ∙ ap (inverse E) (box-crisp-path (fe e))
                    ∙ retraction E (box g′)

  -- Functions from X : Set a into D : Set (a ⊔ L): extensionality at
  -- exactly these two levels. FunExtAt a does not cover it.
  recLarge-unique : (@♭ fe : FunExt₂ a (a ⊔ L))
                  → (@♭ g g′ : S → D) (@♭ e : (x : X) → g (η₀ x) ≡ g′ (η₀ x))
                  → (z : S) → g z ≡ g′ z
  recLarge-unique fe g g′ e z = ap (λ w → counit w z) (boxed fe g g′ e)

------------------------------------------------------------------------
-- 3. The two representations. LargeElimination (fable-impl-02) is the
--    pointwise form: a recursor, its rule and pointwise uniqueness as three
--    crisp fields. Under the mixed extensionality they are interderivable,
--    with the same carrier and unit on both sides.

module _ {@♭ a : Level} (@♭ L : Level) {@♭ X S : Set a} {@♭ η₀ : X → S}
  (@♭ fe : FunExt₂ a (a ⊔ L)) where

  to-pointwise : (@♭ c : LargeTerminalUP L X S η₀) → LargeElimination L S η₀
  to-pointwise c = large
    (λ D D-set D-discrete → At.recLarge L c D D-set D-discrete)
    (λ D D-set D-discrete → At.recLarge-η L c D D-set D-discrete)
    (λ D D-set D-discrete → At.recLarge-unique L c D D-set D-discrete fe)

  module FromPointwise (@♭ up : LargeElimination L S η₀)
    (@♭ D : Set (a ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

    private
      r : (@♭ f : X → D) → S → D
      r = large-rec L S η₀ up D D-set D-discrete

      inv : ♭ (X → D) → ♭ (S → D)
      inv (box f) = box (r f)

      sec : (v : ♭ (X → D)) → precompose L X S η₀ D (inv v) ≡ v
      sec (box f) = box-crisp-path
        (fe (large-rec-η L S η₀ up D D-set D-discrete f))

      ret : (w : ♭ (S → D)) → inv (precompose L X S η₀ D w) ≡ w
      ret (box g) = box-crisp-path
        (fe (large-unique L S η₀ up D D-set D-discrete
              (r (λ x → g (η₀ x))) g
              (large-rec-η L S η₀ up D D-set D-discrete (λ x → g (η₀ x)))))

    is-equiv : IsEquiv (precompose L X S η₀ D)
    is-equiv = quasi-inverse inv sec ret

  from-pointwise : (@♭ up : LargeElimination L S η₀) → LargeTerminalUP L X S η₀
  from-pointwise up D D-set D-discrete = FromPointwise.is-equiv up D D-set D-discrete

------------------------------------------------------------------------
-- 4. Restriction to a smaller ceiling. The ceiling a ⊔ l ⊔ r is restricted
--    to a ⊔ l; carrier and unit are untouched. A target D of the smaller
--    universe is raised, the certificate is used at Raise r D, and the
--    result is lowered. No function extensionality: lower (raise y) is y
--    by computation, and the other composite is never needed.

module Restrict {@♭ a : Level} (@♭ l r : Level) {@♭ X S : Set a} {@♭ η₀ : X → S}
  (@♭ c : LargeTerminalUP (l ⊔ r) X S η₀) where

  module Target (@♭ D : Set (a ⊔ l)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

    private
      D̂ : Set (a ⊔ l ⊔ r)
      D̂ = Raise r D

      E : IsEquiv (precompose (l ⊔ r) X S η₀ D̂)
      E = c D̂ (raise-set D-set) (raise-discrete D-discrete)

      up : {@♭ Z : Set a} → ♭ (Z → D) → ♭ (Z → D̂)
      up = flat-map (λ g z → raise (g z))

      down : {@♭ Z : Set a} → ♭ (Z → D̂) → ♭ (Z → D)
      down = flat-map (λ g z → lower (g z))

      down-up : {@♭ Z : Set a} (w : ♭ (Z → D)) → down (up w) ≡ w
      down-up (box g) = refl

      below : (w : ♭ (S → D̂))
            → precompose l X S η₀ D (down w) ≡ down (precompose (l ⊔ r) X S η₀ D̂ w)
      below (box g) = refl

      above : (w : ♭ (S → D))
            → up (precompose l X S η₀ D w) ≡ precompose (l ⊔ r) X S η₀ D̂ (up w)
      above (box g) = refl

      inv : ♭ (X → D) → ♭ (S → D)
      inv v = down (inverse E (up v))

      sec : (v : ♭ (X → D)) → precompose l X S η₀ D (inv v) ≡ v
      sec v = below (inverse E (up v))
            ∙ ap down (section E (up v))
            ∙ down-up v

      ret : (w : ♭ (S → D)) → inv (precompose l X S η₀ D w) ≡ w
      ret w = ap (λ t → down (inverse E t)) (above w)
            ∙ ap down (retraction E (up w))
            ∙ down-up w

    is-equiv : IsEquiv (precompose l X S η₀ D)
    is-equiv = quasi-inverse inv sec ret

  restrict : LargeTerminalUP l X S η₀
  restrict D D-set D-discrete = Target.is-equiv D D-set D-discrete

------------------------------------------------------------------------
-- 5. The old interface. For a shape datum s with a certificate at any
--    ceiling, the certificate restricted to the level of s gives a recursor
--    on the SAME carrier ʃ s for the SAME unit η s. It agrees pointwise with
--    the recursor s already has, by the uniqueness s already has. The two
--    are different terms; no judgmental equality is claimed or needed.

module Old {@♭ a : Level} (@♭ L : Level) {@♭ X : Set a}
  (@♭ s : ShapeData X) (@♭ c : LargeOn L s) where

  same-level : LargeOn lzero s
  same-level = Restrict.restrict lzero L c

  module _ (@♭ D : Set a) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

    private
      module A = At lzero same-level D D-set D-discrete

    rec-agrees : (@♭ f : X → D) (z : ʃ s)
               → A.recLarge f z ≡ rec s D D-set D-discrete f z
    rec-agrees f = unique s D D-set D-discrete
      (A.recLarge f) (rec s D D-set D-discrete f)
      (λ x → A.recLarge-η f x ∙ sym (rec-η s D D-set D-discrete f x))

-- Conversely a shape datum has the certificate at its own level, by
-- from-pointwise and LargeElimination.own. A larger ceiling is not derived.
own-level : {@♭ a : Level} {@♭ X : Set a} (@♭ fe : FunExt₂ a a)
          → (@♭ s : ShapeData X) → LargeOn lzero s
own-level {a = a} fe s = from-pointwise lzero fe
  (large (rec s) (rec-η s) (unique s))

-- Shape data from a certificate at the level of the source alone.
module Data {@♭ a : Level} {@♭ X S : Set a} {@♭ η₀ : X → S}
  (@♭ S-set : IsSet S) (@♭ S-discrete : Discrete S)
  (@♭ fe : FunExt₂ a a) (@♭ c : LargeTerminalUP lzero X S η₀) where

  data-from : ShapeData X
  data-from = shape-data S S-set S-discrete η₀
    (λ D D-set D-discrete → At.recLarge lzero c D D-set D-discrete)
    (λ D D-set D-discrete → At.recLarge-η lzero c D D-set D-discrete)
    (λ D D-set D-discrete → At.recLarge-unique lzero c D D-set D-discrete fe)

------------------------------------------------------------------------
-- 6. Transfer along a unit-preserving equivalence of carriers. An
--    equivalence of carriers without the unit law is not enough, and none
--    is accepted here.

module Transfer {@♭ a : Level} (@♭ L : Level) {@♭ X S S′ : Set a}
  {@♭ η₀ : X → S} {@♭ η₀′ : X → S′}
  (@♭ fe : FunExt₂ a (a ⊔ L))
  (@♭ e : S → S′) (@♭ e-equiv : IsEquiv e)
  (@♭ e-η : (x : X) → e (η₀ x) ≡ η₀′ x)
  (@♭ c : LargeTerminalUP L X S η₀) where

  module Target (@♭ D : Set (a ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

    private
      E : IsEquiv (precompose L X S η₀ D)
      E = c D D-set D-discrete

      e⁻¹ : S′ → S
      e⁻¹ = inverse e-equiv

      back : (x : X) → e⁻¹ (η₀′ x) ≡ η₀ x
      back x = sym (ap e⁻¹ (e-η x)) ∙ retraction e-equiv (η₀ x)

      along : ♭ (S → D) → ♭ (S′ → D)
      along = flat-map (λ g z′ → g (e⁻¹ z′))

      inv : ♭ (X → D) → ♭ (S′ → D)
      inv v = along (inverse E v)

      -- Precomposition with the new unit after `along` is precomposition
      -- with the old unit.
      old-unit : (@♭ w : ♭ (S → D))
               → precompose L X S′ η₀′ D (along w) ≡ precompose L X S η₀ D w
      old-unit (box g) = box-crisp-path (fe (λ x → ap g (back x)))

      sec : (v : ♭ (X → D)) → precompose L X S′ η₀′ D (inv v) ≡ v
      sec (box f) = old-unit (inverse E (box f)) ∙ section E (box f)

      ret : (w : ♭ (S′ → D)) → inv (precompose L X S′ η₀′ D w) ≡ w
      ret (box g′) =
        ap (λ t → along (inverse E t))
           (box-crisp-path (fe (λ x → sym (ap g′ (e-η x)))))
        ∙ ap along (retraction E (box (λ z → g′ (e z))))
        ∙ box-crisp-path (fe (λ z′ → ap g′ (section e-equiv z′)))

    is-equiv : IsEquiv (precompose L X S′ η₀′ D)
    is-equiv = quasi-inverse inv sec ret

  transfer : LargeTerminalUP L X S′ η₀′
  transfer D D-set D-discrete = Target.is-equiv D D-set D-discrete

------------------------------------------------------------------------
-- 7. The raised source. A certificate for (S, η₀) at ceiling a ⊔ L gives
--    shape data for Raise L X in the larger universe, with carrier
--    Raise L S and the raised unit. Comparing it with an independently
--    chosen shape of Raise L X is then GlobalChoice at one level.

module RaisedData {@♭ a : Level} (@♭ L : Level) {@♭ X S : Set a} {@♭ η₀ : X → S}
  (@♭ S-set : IsSet S) (@♭ S-discrete : Discrete S)
  (@♭ fe : FunExt₂ a (a ⊔ L)) (@♭ c : LargeTerminalUP L X S η₀) where

  private
    raised-unit : Raise L X → Raise L S
    raised-unit r = raise (η₀ (lower r))

    module _ (@♭ D : Set (a ⊔ L)) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D) where

      private
        module A = At L c D D-set D-discrete

      r-rec : (@♭ f : Raise L X → D) → Raise L S → D
      r-rec f z = A.recLarge (λ x → f (raise x)) (lower z)

      r-rec-η : (@♭ f : Raise L X → D) (r : Raise L X)
              → r-rec f (raised-unit r) ≡ f r
      r-rec-η f r = A.recLarge-η (λ x → f (raise x)) (lower r)
                  ∙ ap f (raise-lower r)

      r-unique : (@♭ g g′ : Raise L S → D)
               → (@♭ e : (r : Raise L X) → g (raised-unit r) ≡ g′ (raised-unit r))
               → (z : Raise L S) → g z ≡ g′ z
      r-unique g g′ e (raise z) =
        A.recLarge-unique fe (λ z → g (raise z)) (λ z → g′ (raise z)) (λ x → e (raise x)) z

  raised-data : ShapeData (Raise L X)
  raised-data = shape-data (Raise L S) (raise-set S-set) (raise-discrete S-discrete)
    raised-unit r-rec r-rec-η r-unique

------------------------------------------------------------------------
-- 8. The action on a map into a type of the larger universe, and the
--    coaugmentation of T = shape ∘ ♯. The target is given by its carrier
--    and unit, so the statements apply to ClosedBridge.Existence before any
--    function extensionality is supplied, as well as to shape data. The
--    target carrier stays where it is; nothing is raised or lowered.

module MapShape {@♭ a : Level} (@♭ L : Level) {@♭ X : Set a} {@♭ Y : Set (a ⊔ L)}
  {@♭ S : Set a} {@♭ η₀ : X → S} (@♭ c : LargeTerminalUP L X S η₀)
  (@♭ S′ : Set (a ⊔ L)) (@♭ S′-set : IsSet S′) (@♭ S′-discrete : Discrete S′)
  (@♭ η₀′ : Y → S′) (@♭ f : X → Y) where

  mapShape : S → S′
  mapShape = At.recLarge L c S′ S′-set S′-discrete (λ x → η₀′ (f x))

  mapShape-η : (x : X) → mapShape (η₀ x) ≡ η₀′ (f x)
  mapShape-η = At.recLarge-η L c S′ S′-set S′-discrete (λ x → η₀′ (f x))

module SharpComposite {@♭ a : Level} (@♭ L : Level)
  {@♭ A : Set a} {@♭ B : Set (a ⊔ L)}
  {@♭ SA : Set a} {@♭ ηA : ♯ A → SA} (@♭ c : LargeTerminalUP L (♯ A) SA ηA)
  (@♭ SB : Set (a ⊔ L)) (@♭ SB-set : IsSet SB) (@♭ SB-discrete : Discrete SB)
  (@♭ ηB : ♯ B → SB) (@♭ h : A → B) where

  private
    module M = MapShape L c SB SB-set SB-discrete ηB (sharp-map h)

  -- The coaugmentations A → T A and B → T B.
  unit-A : A → SA
  unit-A x = ηA (sharp-unit x)

  unit-B : B → SB
  unit-B y = ηB (sharp-unit y)

  -- T h : T A → T B, with T A small and T B in the larger universe.
  T-map : SA → SB
  T-map = M.mapShape

  T-natural : (x : A) → T-map (unit-A x) ≡ unit-B (h x)
  T-natural x = M.mapShape-η (sharp-unit x) ∙ ap ηB (sharp-map-unit h x)
