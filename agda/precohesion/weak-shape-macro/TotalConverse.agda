{-# OPTIONS --cohesion --without-K --flat-split #-}

-- From terminal shape data of a total space to a relative reflection.
-- The converse of TotalBridge.TotalData. Postulate-free.
-- Claude (Fable), 13 November 2026; fable-impl-06. HANDOFF-06 item 6
-- ("R36 converse"); FABLE-REVIEW-03.txt section 8.1.
--
-- Let Γ be a closed discrete SET, A a family over it, and s terminal shape
-- data of the total space Σ Γ A. Then
--
--   Converse.relative : RelativeShapeOver Γ dΓ A
--
-- with total space the carrier ʃ s, unit the unit η s, and projection the
-- recursor of s applied to the first projection Σ Γ A → Γ. Nothing is
-- chosen: carrier and unit are those of s.
--
-- Proof. A CRISP map over Γ from Σ Γ A into a discrete D → Γ with set
-- fibres has a crisp underlying map into D, and D is a set because Γ is.
-- (An ordinary map over Γ is not made crisp: the inverse is defined on
-- boxed maps, by matching on the box.) The recursor of s extends the
-- underlying map to ʃ s; the extension lies over Γ because both
-- composites to Γ agree on units (uniqueness for the target Γ). The two
-- inverse laws hold pointwise by the computation rule and by uniqueness
-- for the target D, and become equalities of maps over Γ by function
-- extensionality, the triangles being paths in the set Γ. Adjointify
-- turns the two-sided inverse into the equivalence that the relative
-- schema asks for.
--
-- With TotalBridge this shows that, over a discrete set, a relative
-- reflection and terminal shape data of the total space are the same
-- thing with the same carrier and unit (for both round trips the carriers
-- and the units are checked by refl at the end; the projection is
-- identified pointwise, by uniqueness). In particular ONE closed shape
-- axiom for Σ Γ A gives the relative reflection of A over Γ, and, where Γ
-- has decidable equality, terminal shape data of every fibre
-- (DecidableBase.Fibre).
--
-- What this does NOT give: anything over a base that is not a set (there
-- the total space of a relative reflection is not the terminal shape), and
-- no shape data for a total space from shape data of the fibres. Nor is
-- it a new capability of the frontend: the construction takes its shape
-- data as an argument, for any crisp Γ and A, and supplies none.
--
-- fable-impl-07: the three sentences above marked by M6-FOUNDATION-SOURCE-
-- AUDIT-01 section 7 (a), (b), (d) are reworded; comments only. Its remark
-- (c) stands: the extension Target.factor and its computation rule do not
-- use fe, but they are stated inside the module that takes fe, and no
-- separate entry point without fe is exported or tested.
module TotalConverse where

open import Foundations
import RelativeSliceShape as R
open R using
  (RelativeShapeOver; shape-over; MapOver; over-map; function; triangle;
   SetFibers; precomposeOver)
open import PullbackSetFibers using (retract-set)
open import NativeSharp using (box-crisp-path)
open import ShapeChoice using (FunExtAt)
open import Adjointify using (quasi-inverse)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; unique)
open import TotalBridge using (Σ-set; module TotalData)

private
  cancel : ∀ {a} {A : Set a} {x y : A} (c : x ≡ y) → sym c ∙ c ≡ refl
  cancel refl = refl

  -- A proposition is a set.
  prop-set : ∀ {a} {A : Set a} → IsProp A → IsSet A
  prop-set {A = A} h x y p q = normal p ∙ sym (normal q)
    where
    normal : {y : A} (r : x ≡ y) → r ≡ sym (h x x) ∙ h x y
    normal refl = sym (cancel (h x x))

module _ {@♭ ℓ : Level} where

  module Converse
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
    {@♭ A : Γ → Set ℓ} (@♭ s : ShapeData (Σ Γ A)) where

    S : Set ℓ
    S = ʃ s

    -- The projection: the first projection of the total space, extended.
    p : S → Γ
    p = rec s Γ Γ-set dΓ fst

    p-η : (a : Σ Γ A) → p (η s a) ≡ fst a
    p-η = rec-η s Γ Γ-set dΓ fst

    p-set-fibers : SetFibers p
    p-set-fibers γ = Σ-set (ʃ-set s) (λ z → prop-set (Γ-set (p z) γ))

    module Target
      (@♭ D : Set ℓ) (@♭ D-discrete : Discrete D)
      (@♭ q : D → Γ) (@♭ qf : SetFibers q) where

      -- Over a set, a type with set fibres is a set.
      D-set : IsSet D
      D-set = retract-set {B = Σ Γ (Fiber q)}
        (λ d → q d , (d , refl)) (λ w → fst (snd w)) (λ _ → refl)
        (Σ-set Γ-set qf)

      pre : MapOver p q → MapOver (fst {B = A}) q
      pre = precomposeOver Γ A S p (η s) p-η D q

      extend : (@♭ f : MapOver (fst {B = A}) q) → S → D
      extend f = rec s D D-set D-discrete (function f)

      extend-η : (@♭ f : MapOver (fst {B = A}) q) (a : Σ Γ A)
               → extend f (η s a) ≡ function f a
      extend-η f = rec-η s D D-set D-discrete (function f)

      -- The extension lies over Γ: both composites agree on units.
      extend-over : (@♭ f : MapOver (fst {B = A}) q) (z : S)
                  → q (extend f z) ≡ p z
      extend-over f = unique s Γ Γ-set dΓ (λ z → q (extend f z)) p
        (λ a → ap q (extend-η f a) ∙ triangle f a ∙ sym (p-η a))

      factor : (@♭ f : MapOver (fst {B = A}) q) → MapOver p q
      factor f = over-map (extend f) (extend-over f)

      back : ♭ (MapOver (fst {B = A}) q) → ♭ (MapOver p q)
      back (box f) = box (factor f)

      -- Two maps over Γ with pointwise equal functions are equal: the
      -- triangles are paths in the set Γ.
      over-path : {X : Set ℓ} {r : X → Γ} (k k′ : MapOver r q)
                → ((x : X) → function k x ≡ function k′ x) → k ≡ k′
      over-path {X} {r} (over-map g t) (over-map g′ t′) h = step (fe h) t′
        where
        step : {g″ : X → D} → g ≡ g″ → (t″ : (x : X) → q (g″ x) ≡ r x)
             → over-map g t ≡ over-map g″ t″
        step refl t″ = ap (over-map g) (fe (λ x → Γ-set _ _ (t x) (t″ x)))

      sec : (y : ♭ (MapOver (fst {B = A}) q)) → flat-map pre (back y) ≡ y
      sec (box f) = box-crisp-path
        (over-path (pre (factor f)) f (λ a → extend-η f a))

      ret : (x : ♭ (MapOver p q)) → back (flat-map pre x) ≡ x
      ret (box k) = box-crisp-path
        (over-path (factor (pre k)) k
          (unique s D D-set D-discrete (extend (pre k)) (function k)
            (λ a → extend-η (pre k) a)))

      universal : IsEquiv (flat-map pre)
      universal = quasi-inverse back sec ret

    -- The relative reflection, with the carrier and the unit of s.
    relative : RelativeShapeOver Γ dΓ A
    relative = shape-over S (ʃ-discrete s) p p-set-fibers (η s) p-η
      (λ D D-discrete q qf → Target.universal D D-discrete q qf)

    -- Round trip through TotalBridge: the same carrier and the same unit,
    -- on the nose.
    round-trip-carrier : ʃ (TotalData.total-data fe Γ-set relative) ≡ ʃ s
    round-trip-carrier = refl

    round-trip-unit : (a : Σ Γ A)
                    → η (TotalData.total-data fe Γ-set relative) a ≡ η s a
    round-trip-unit a = refl

  -- The other round trip: from a relative reflection to shape data of the
  -- total space and back. Carrier, unit and projection are those of K,
  -- the projection up to the pointwise path that uniqueness gives.
  module RoundTrip
    (@♭ fe : FunExtAt ℓ)
    {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
    {@♭ A : Γ → Set ℓ} (@♭ K : RelativeShapeOver Γ dΓ A) where

    private
      s : ShapeData (Σ Γ A)
      s = TotalData.total-data fe Γ-set K

      K′ : RelativeShapeOver Γ dΓ A
      K′ = Converse.relative fe {dΓ = dΓ} Γ-set s

    same-total : R.Output.Total K′ ≡ R.Output.Total K
    same-total = refl

    same-unit : (a : Σ Γ A) → R.Output.unit K′ a ≡ R.Output.unit K a
    same-unit a = refl

    same-projection : (z : R.Output.Total K)
                    → R.Output.projection K′ z ≡ R.Output.projection K z
    same-projection = unique s Γ Γ-set dΓ
      (R.Output.projection K′) (R.Output.projection K)
      (λ a → Converse.p-η fe {dΓ = dΓ} Γ-set s a
             ∙ sym (R.Output.unit-over K a))
