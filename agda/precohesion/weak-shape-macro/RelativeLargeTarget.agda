{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The RELATIVE larger-target certificate: over a discrete SET base, the
-- universal property of a relative reflection against targets of a larger
-- universe, from a supplied terminal certificate for the total source.
-- Claude (Fable), 13 November 2026; after fable-impl-15 (HANDOFF-32;
-- RELATIVE-LARGE-UP-IMPLEMENTATION-REVIEW-01, whose plan this follows;
-- NEXT-NATIVE-CLASSIFIER-GATE-01 section 5; FOUNDATION-COMPLETION-GATES-01
-- G3; FABLE-REVIEW-05 section 5 item 4). Postulate-free; no reflection; no
-- capture; it declares nothing. A conditional theorem of the library, not
-- a schema and not a theorem of the paper.
--
-- LEVELS. ℓ is the level of the base, the source, the carrier, the
-- projection and the unit; L is a further level; targets are in
-- Set (ℓ ⊔ L). Nothing of level ℓ is raised.
--
--   LargeSliceUP L Γ A S p η η-over
--     = (@♭ D : Set (ℓ ⊔ L)) (@♭ dD : Discrete D)
--       (@♭ q : D → Γ) (@♭ qf : SetFibersM q)
--       → IsEquiv (flat-map (precomposeOverM L Γ A S p η η-over D q))
--
-- the statement of RelativeSliceShape.SliceUniversal with the target in
-- the larger universe: precomposition with the unit, on BOXED maps over
-- the base, is an equivalence.
--
--   RelativeLargeOn L K   that statement for the total space, projection,
--                         unit and unit law that K ALREADY has
--
-- This is a TYPE. It does not ask the base to be a set. The DERIVATION
-- from a terminal certificate does (Core, the two adapters, AtSmaller);
-- SameLevel does not, and works over any base.
--
--   Factor, FactorOn      a certificate in use: the factorisation of a
--                         crisp map over the base through the unit, and
--                         its rule on units; no extensionality
--
-- THE THEOREM (Core). Crisp data: a discrete set Γ : Set ℓ; A : Γ → Set ℓ
-- with ARBITRARY fibres; terminal shape data s of Σ Γ A; a projection
-- p : ʃ s → Γ with  p (η s a) ≡ fst a ; function extensionality at level ℓ;
-- and a terminal certificate  c : LargeOn L s. Then
--   Core.certificate : LargeSliceUP L Γ A (ʃ s) p (η s) p-η
-- on the SAME carrier ʃ s, the SAME unit η s and the GIVEN projection p.
--
-- Proof, for crisp D, dD, q, qf.
--   1. D is a set: a retract of Σ Γ (Fiber q), a Σ of sets over the set Γ.
--      This is where the base has to be a set. No extensionality.
--   2. E = c D D-set dD, an equivalence of boxed TERMINAL map spaces.
--      For a crisp map f over Γ,  extend f = counit (inverse E (box (the
--      function of f))) : ʃ s → D.
--   3. E gives an equality of FUNCTIONS, extend f ∘ η s ≡ function of f
--      (function-section): the section law of E under counit. It is kept
--      as an equality of functions.
--   4. extend f lies over Γ: q ∘ extend f and p agree on units, and s has
--      uniqueness for the SMALL discrete set Γ (extend-over). Uniqueness
--      of s is never applied to D.
--   5. back (box f) = box (extend f with that triangle).
--   6. For a crisp k over p, the retraction law of E under counit is an
--      equality of functions  extend (k ∘ η s) ≡ function of k
--      (function-retraction).
--   7. Two maps over Γ with EQUAL functions are equal (over-path): by
--      path induction the functions are one, and the two triangles are
--      functions from a type of Set ℓ into paths of the set Γ : Set ℓ,
--      equal pointwise, hence equal by extensionality AT LEVEL ℓ.
--   8. 3 and 6 with 7, boxed (box-crisp-path), are the two inverse laws;
--      Adjointify makes the equivalence. No sethood of the boxed map
--      spaces is used.
--
-- EXTENSIONALITY LEDGER. FunExtAt ℓ, crisp, in step 7 only, for the
-- triangle fields. No extensionality for functions into Set (ℓ ⊔ L): the
-- two function equalities come from the inverse laws of E as they are.
-- Had they been weakened to pointwise equalities, FunExt₂ ℓ (ℓ ⊔ L) would
-- be needed to get them back. The fact is that NO HYPOTHESIS of mixed
-- extensionality is taken or used by this proof. It is not a fact about
-- imports: this module has no DIRECT import of GlobalPropositions, where
-- FunExt₂ is defined, but LargeTarget imports it, so it is in the import
-- closure. LargeTarget.At.recLarge-unique is not used. (fable-impl-17,
-- after M16-SOURCE-REVIEW-01: this replaces "This module does not import
-- GlobalPropositions".)
--
-- THE TWO ADAPTERS.
--   Canonical.relative-large   for  K = TotalConverse.Converse.relative
--       fe Γ-set s : the projection is the recursor of s on fst. From
--       c : LargeOn L s.
--   Direct.relative-large      for a relative reflection K that ALREADY
--       exists, over a set base: s is TotalBridge's total-data fe Γ-set K,
--       whose carrier and unit are the total space and unit of K by
--       computation; the projection and unit law are K's OWN. From
--       c : LargeOn L (total-data fe Γ-set K). K is not replaced, no two
--       shape records are identified, nothing is transported along the
--       path between K's projection and the recursor's.
-- In both, c is CRISP and SUPPLIED. Nothing here makes a certificate at a
-- larger ceiling from shape data, relative or terminal; the terminal
-- certificate at the level of s itself is LargeTarget.own-level, with its
-- own extensionality hypothesis.
--
-- A SMALLER CEILING (AtSmaller). From a terminal certificate at ℓ ⊔ l ⊔ r
-- the relative one at ℓ ⊔ l, by restricting the SUPPLIED terminal
-- certificate (LargeTarget.Restrict) and running the theorem again, on
-- the same carrier, unit and projection. There is NO operation here from
-- a relative certificate alone to one at another ceiling, in either
-- direction, and none between different choices of shape data.
--
-- AT THE CEILING OF THE SOURCE (SameLevel). LargeSliceUP lzero and
-- RelativeSliceShape.SliceUniversal are statements about two records; the
-- two precompositions are conjugate by the fieldwise maps of MixedMapOver,
-- so either statement gives the other (from-universal, to-universal). In
-- particular  relative-own-level K : RelativeLargeOn lzero K  for every
-- K, by K's own universal property, over any base. These are transfers
-- of the SAME precomposition; nothing says that a certificate obtained
-- from Core at ceiling lzero and the one obtained from K are equal as
-- terms.
--
-- NOT OBTAINED: a shape; by the derivation from a terminal certificate, a
-- certificate over a base that is not a set (set fibres over a higher
-- base do not give the set target that a terminal certificate needs; the
-- statement at the ceiling of the source, SameLevel, is not affected and
-- holds over any base: fable-impl-17); promotion of a fibre; stability
-- under substitution; any change of universe of a carrier.
module RelativeLargeTarget where

open import Foundations
import RelativeSliceShape as R
open R using
  (RelativeShapeOver; MapOver; UnitOver; SetFibers; precomposeOver;
   SliceUniversal)
open import MixedMapOver
open import PullbackSetFibers using (retract-set)
open import NativeSharp using (box-crisp-path)
open import ShapeChoice using (FunExtAt)
open import Adjointify using (quasi-inverse)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; unique)
open import TotalBridge using (Σ-set; module TotalData)
open import TotalConverse using (module Converse)
open import LargeTarget using (LargeTerminalUP; LargeOn; precompose; module Restrict)

------------------------------------------------------------------------
-- 1. The statement.

LargeSliceUP : {@♭ ℓ : Level} (@♭ L : Level)
             → (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ)
             → (@♭ S : Set ℓ) (@♭ p : S → Γ)
             → (@♭ η₀ : Σ Γ A → S)
             → (@♭ η-over : UnitOver Γ A S p η₀)
             → Set (lsuc (ℓ ⊔ L))
LargeSliceUP {ℓ} L Γ A S p η₀ η-over =
  (@♭ D : Set (ℓ ⊔ L)) (@♭ D-discrete : Discrete D)
  (@♭ q : D → Γ) (@♭ q-set-fibers : SetFibersM q)
  → IsEquiv (flat-map (precomposeOverM L Γ A S p η₀ η-over D q))

-- For a relative reflection: its own total space, projection, unit and
-- unit law. This makes no new reflection.
RelativeLargeOn : {@♭ ℓ : Level} (@♭ L : Level)
                → {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
                → (@♭ K : RelativeShapeOver Γ dΓ A) → Set (lsuc (ℓ ⊔ L))
RelativeLargeOn L {Γ = Γ} {A = A} K =
  LargeSliceUP L Γ A (R.Output.Total K) (R.Output.projection K)
    (R.Output.unit K) (R.Output.unit-over K)

------------------------------------------------------------------------
-- 2. In use: the factorisation of a crisp map over the base, and its
--    rule on units. The mixed form of RelativeSliceShape.Output.factor,
--    factor-β and factor-on-unit; no extensionality.

module Factor
  {@♭ ℓ : Level} (@♭ L : Level)
  (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ) (@♭ S : Set ℓ) (@♭ p : S → Γ)
  (@♭ η₀ : Σ Γ A → S) (@♭ η-over : UnitOver Γ A S p η₀)
  (@♭ u : LargeSliceUP L Γ A S p η₀ η-over)
  (@♭ D : Set (ℓ ⊔ L)) (@♭ D-discrete : Discrete D)
  (@♭ q : D → Γ) (@♭ qf : SetFibersM q) where

  private
    pre : MapOverM p q → MapOverM (fst {B = A}) q
    pre = precomposeOverM L Γ A S p η₀ η-over D q

    U : IsEquiv (flat-map pre)
    U = u D D-discrete q qf

  factor : (@♭ f : MapOverM (fst {B = A}) q) → MapOverM p q
  factor f = counit (inverse U (box f))

  factor-β : (@♭ f : MapOverM (fst {B = A}) q) → pre (factor f) ≡ f
  factor-β f = sym (flat-map-counit pre (inverse U (box f)))
             ∙ ap counit (section U (box f))

  factor-on-unit : (@♭ f : MapOverM (fst {B = A}) q) (a : Σ Γ A)
                 → functionM (factor f) (η₀ a) ≡ functionM f a
  factor-on-unit f a = ap (λ h → functionM h a) (factor-β f)

-- The same for a relative reflection and a certificate for it.
module FactorOn
  {@♭ ℓ : Level} (@♭ L : Level)
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  (@♭ K : RelativeShapeOver Γ dΓ A) (@♭ u : RelativeLargeOn L K)
  (@♭ D : Set (ℓ ⊔ L)) (@♭ D-discrete : Discrete D)
  (@♭ q : D → Γ) (@♭ qf : SetFibersM q) where

  open Factor L Γ A (R.Output.Total K) (R.Output.projection K)
    (R.Output.unit K) (R.Output.unit-over K) u D D-discrete q qf public

------------------------------------------------------------------------
-- 3. The theorem, for a fixed projection on the carrier of s.

module Core
  {@♭ ℓ : Level} (@♭ L : Level)
  (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} (@♭ dΓ : Discrete Γ) (@♭ Γ-set : IsSet Γ)
  {@♭ A : Γ → Set ℓ} (@♭ s : ShapeData (Σ Γ A))
  (@♭ p : ʃ s → Γ) (@♭ p-η : (a : Σ Γ A) → p (η s a) ≡ fst a)
  (@♭ c : LargeOn L s) where

  module Target
    (@♭ D : Set (ℓ ⊔ L)) (@♭ D-discrete : Discrete D)
    (@♭ q : D → Γ) (@♭ qf : SetFibersM q) where

    -- 1. Over a set, a type with set fibres is a set.
    D-set : IsSet D
    D-set = retract-set {B = Σ Γ (Fiber q)}
      (λ d → q d , (d , refl)) (λ w → fst (snd w)) (λ _ → refl)
      (Σ-set Γ-set qf)

    pre : MapOverM p q → MapOverM (fst {B = A}) q
    pre = precomposeOverM L Γ A (ʃ s) p (η s) p-η D q

    private
      -- 2. The supplied equivalence of boxed terminal map spaces.
      E : IsEquiv (precompose L (Σ Γ A) (ʃ s) (η s) D)
      E = c D D-set D-discrete

    extend : (@♭ f : MapOverM (fst {B = A}) q) → ʃ s → D
    extend f = counit (inverse E (box (functionM f)))

    -- 3. An equality of FUNCTIONS, from the section law of E.
    function-section : (@♭ f : MapOverM (fst {B = A}) q)
                     → (λ a → extend f (η s a)) ≡ functionM f
    function-section f =
      sym (flat-map-counit (λ g a → g (η s a)) (inverse E (box (functionM f))))
      ∙ ap counit (section E (box (functionM f)))

    extend-η : (@♭ f : MapOverM (fst {B = A}) q) (a : Σ Γ A)
             → extend f (η s a) ≡ functionM f a
    extend-η f = happly (function-section f)

    -- 4. The extension lies over Γ: uniqueness of s for the SMALL target Γ.
    extend-over : (@♭ f : MapOverM (fst {B = A}) q) (z : ʃ s)
                → q (extend f z) ≡ p z
    extend-over f = unique s Γ Γ-set dΓ (λ z → q (extend f z)) p
      (λ a → ap q (extend-η f a) ∙ triangleM f a ∙ sym (p-η a))

    factor : (@♭ f : MapOverM (fst {B = A}) q) → MapOverM p q
    factor f = over-mapM (extend f) (extend-over f)

    -- 5. Defined on boxed maps, by matching on the box. An ordinary map
    --    over Γ is not made crisp.
    back : ♭ (MapOverM (fst {B = A}) q) → ♭ (MapOverM p q)
    back (box f) = box (factor f)

    -- 6. An equality of FUNCTIONS, from the retraction law of E.
    function-retraction : (@♭ k : MapOverM p q)
                        → extend (pre k) ≡ functionM k
    function-retraction k = ap counit (retraction E (box (functionM k)))

    -- 7. Maps over Γ with EQUAL functions are equal. Extensionality at
    --    level ℓ, for the triangles alone: functions from X : Set ℓ into
    --    paths of the set Γ : Set ℓ.
    over-path : {X : Set ℓ} {r : X → Γ} (k k′ : MapOverM r q)
              → functionM k ≡ functionM k′ → k ≡ k′
    over-path {X} {r} (over-mapM g t) (over-mapM g′ t′) e = step e t′
      where
      step : {g″ : X → D} → g ≡ g″ → (t″ : (x : X) → q (g″ x) ≡ r x)
           → over-mapM g t ≡ over-mapM g″ t″
      step refl t″ = ap (over-mapM g) (fe (λ x → Γ-set _ _ (t x) (t″ x)))

    -- 8. The two inverse laws, and the equivalence.
    sec : (y : ♭ (MapOverM (fst {B = A}) q)) → flat-map pre (back y) ≡ y
    sec (box f) = box-crisp-path
      (over-path (pre (factor f)) f (function-section f))

    ret : (x : ♭ (MapOverM p q)) → back (flat-map pre x) ≡ x
    ret (box k) = box-crisp-path
      (over-path (factor (pre k)) k (function-retraction k))

    universal : IsEquiv (flat-map pre)
    universal = quasi-inverse back sec ret

  certificate : LargeSliceUP L Γ A (ʃ s) p (η s) p-η
  certificate D D-discrete q qf = Target.universal D D-discrete q qf

------------------------------------------------------------------------
-- 4. The two adapters.

-- For the relative reflection that TotalConverse makes from s: carrier and
-- unit of s, projection the recursor of s on the first projection.
module Canonical
  {@♭ ℓ : Level} (@♭ L : Level)
  (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
  {@♭ A : Γ → Set ℓ} (@♭ s : ShapeData (Σ Γ A))
  (@♭ c : LargeOn L s) where

  relative-large : RelativeLargeOn L (Converse.relative fe {dΓ = dΓ} Γ-set s)
  relative-large = Core.certificate L fe dΓ Γ-set s
    (Converse.p fe {dΓ = dΓ} Γ-set s) (Converse.p-η fe {dΓ = dΓ} Γ-set s) c

-- For a relative reflection that already exists, over a set base. The
-- shape data are TotalBridge's; their carrier and unit are the total
-- space and the unit of K by computation, so the conclusion is about K
-- itself, with its own projection and unit law.
module Direct
  {@♭ ℓ : Level} (@♭ L : Level)
  (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
  {@♭ A : Γ → Set ℓ} (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ c : LargeOn L (TotalData.total-data fe Γ-set K)) where

  relative-large : RelativeLargeOn L K
  relative-large = Core.certificate L fe dΓ Γ-set
    (TotalData.total-data fe Γ-set K)
    (R.Output.projection K) (R.Output.unit-over K) c

------------------------------------------------------------------------
-- 5. A smaller ceiling: restrict the SUPPLIED terminal certificate, then
--    the theorem again. Same carrier, unit and projection.

module AtSmaller
  {@♭ ℓ : Level} (@♭ l r : Level)
  (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} (@♭ dΓ : Discrete Γ) (@♭ Γ-set : IsSet Γ)
  {@♭ A : Γ → Set ℓ} (@♭ s : ShapeData (Σ Γ A))
  (@♭ p : ʃ s → Γ) (@♭ p-η : (a : Σ Γ A) → p (η s a) ≡ fst a)
  (@♭ c : LargeOn (l ⊔ r) s) where

  restricted : LargeOn l s
  restricted = Restrict.restrict l r c

  certificate : LargeSliceUP l Γ A (ʃ s) p (η s) p-η
  certificate = Core.certificate l fe dΓ Γ-set s p p-η restricted

------------------------------------------------------------------------
-- 6. At the ceiling of the source: the mixed statement and the old one
--    are about conjugate precompositions.

module SameLevel
  {@♭ ℓ : Level}
  (@♭ Γ : Set ℓ) (@♭ A : Γ → Set ℓ) (@♭ S : Set ℓ) (@♭ p : S → Γ)
  (@♭ η₀ : Σ Γ A → S) (@♭ η-over : UnitOver Γ A S p η₀) where

  module Target (@♭ D : Set ℓ) (@♭ q : D → Γ) where

    private
      old : MapOver p q → MapOver (fst {B = A}) q
      old = precomposeOver Γ A S p η₀ η-over D q

      new : MapOverM p q → MapOverM (fst {B = A}) q
      new = precomposeOverM lzero Γ A S p η₀ η-over D q

      -- The fieldwise maps on boxes; both round trips by computation.
      up : {@♭ X : Set ℓ} {@♭ r : X → Γ} → ♭ (MapOver r q) → ♭ (MapOverM r q)
      up = flat-map from-old

      down : {@♭ X : Set ℓ} {@♭ r : X → Γ} → ♭ (MapOverM r q) → ♭ (MapOver r q)
      down = flat-map to-old

      up-down : {@♭ X : Set ℓ} {@♭ r : X → Γ} (w : ♭ (MapOverM r q))
              → up (down w) ≡ w
      up-down (box k) = refl

      down-up : {@♭ X : Set ℓ} {@♭ r : X → Γ} (w : ♭ (MapOver r q))
              → down (up w) ≡ w
      down-up (box k) = refl

      -- The commuting square of MixedMapOver, on boxes.
      new-up : (w : ♭ (MapOver p q)) → flat-map new (up w) ≡ up (flat-map old w)
      new-up (box k) = refl

      old-down : (w : ♭ (MapOverM p q))
               → flat-map old (down w) ≡ down (flat-map new w)
      old-down (box k) = refl

    module FromOld (U : IsEquiv (flat-map old)) where

      private
        inv : ♭ (MapOverM (fst {B = A}) q) → ♭ (MapOverM p q)
        inv w = up (inverse U (down w))

        sec : (w : ♭ (MapOverM (fst {B = A}) q)) → flat-map new (inv w) ≡ w
        sec w = new-up (inverse U (down w))
              ∙ ap up (section U (down w))
              ∙ up-down w

        ret : (w : ♭ (MapOverM p q)) → inv (flat-map new w) ≡ w
        ret w = ap (λ t → up (inverse U t)) (sym (old-down w))
              ∙ ap up (retraction U (down w))
              ∙ up-down w

      is-equiv : IsEquiv (flat-map new)
      is-equiv = quasi-inverse inv sec ret

    module ToOld (U : IsEquiv (flat-map new)) where

      private
        inv : ♭ (MapOver (fst {B = A}) q) → ♭ (MapOver p q)
        inv w = down (inverse U (up w))

        sec : (w : ♭ (MapOver (fst {B = A}) q)) → flat-map old (inv w) ≡ w
        sec w = old-down (inverse U (up w))
              ∙ ap down (section U (up w))
              ∙ down-up w

        ret : (w : ♭ (MapOver p q)) → inv (flat-map old w) ≡ w
        ret w = ap (λ t → down (inverse U t)) (sym (new-up w))
              ∙ ap down (retraction U (up w))
              ∙ down-up w

      is-equiv : IsEquiv (flat-map old)
      is-equiv = quasi-inverse inv sec ret

  -- SetFibersM at one level is SetFibers, and ℓ ⊔ lzero is ℓ: the two
  -- statements quantify over the same targets.
  from-universal : SliceUniversal Γ A S p η₀ η-over
                 → LargeSliceUP lzero Γ A S p η₀ η-over
  from-universal U D D-discrete q qf =
    Target.FromOld.is-equiv D q (U D D-discrete q qf)

  to-universal : LargeSliceUP lzero Γ A S p η₀ η-over
               → SliceUniversal Γ A S p η₀ η-over
  to-universal U D D-discrete q qf =
    Target.ToOld.is-equiv D q (U D D-discrete q qf)

-- Every relative reflection has the mixed statement at the ceiling of its
-- own level, over any base: it is its own universal property.
relative-own-level :
  {@♭ ℓ : Level} {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} {@♭ A : Γ → Set ℓ}
  → (@♭ K : RelativeShapeOver Γ dΓ A) → RelativeLargeOn lzero K
relative-own-level {Γ = Γ} {A = A} K =
  SameLevel.from-universal Γ A (R.Output.Total K) (R.Output.projection K)
    (R.Output.unit K) (R.Output.unit-over K) (R.Output.universal K)
