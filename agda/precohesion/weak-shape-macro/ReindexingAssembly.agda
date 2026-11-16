{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The canonical reindexing comparison in its total form, and the passage
-- between the total form and the fibre form. Postulate-free; no function
-- extensionality. Claude (Fable), 13 November 2026; fable-impl-08;
-- GENERIC-MAIN-SCHEMA-ADEQUACY-01 section 7, FABLE-REVIEW-05 section 4
-- (fields A6 and A7), REFLECTION-ISSUES R31.
--
-- ShapeReindexing.Comparison constructs, for a family A over a discrete Γ,
-- a map f : Γ′ → Γ and two relative reflections (of A over Γ and of A ∘ f
-- over Γ′), the canonical map over Γ′
--
--     comparison-total : Total reshaped → Pullback (projection shaped) f
--
-- and its fibres  comparison γ′. The conclusion of the local-connectedness
-- theorem is stated there in fibre form: ComparisonIsEquivalence. A proof
-- that works with whole objects, as the ordinary proof does, concludes that
-- comparison-total is an equivalence:  shape (X ×_B C) → shape X ×_B C.
-- This module names that statement and shows that the two forms agree:
--
--   TotalComparisonIsEquivalence      IsEquiv comparison-total
--   FromFibres.total                  fibre form ⇒ total form
--   FromTotal.fibres                  total form ⇒ fibre form, for a SET Γ′
--
-- Neither direction asserts that the comparison IS an equivalence. Both
-- are about the one canonical map of ShapeReindexing, with its unit law
-- comparison-on-unit unchanged; no other equivalence of the two carriers is
-- introduced. The first direction needs no sethood. The second uses that
-- Γ′ is a set, to compare two proofs that a point lies over γ′.
module ReindexingAssembly where

open import Foundations
open import RelativeSliceShape
open import PullbackSetFibers using (transport)
open import FlatContext using (fiber-path)
open import Adjointify using (quasi-inverse)
open import ShapeReindexing using (module Comparison)

private
  Σ-path : ∀ {a b} {A : Set a} {B : A → Set b}
         → {x x′ : A} {y : B x} {y′ : B x′}
         → (q : x ≡ x′) → transport B q y ≡ y′
         → _≡_ {A = Σ A B} (x , y) (x′ , y′)
  Σ-path refl refl = refl

  snd-path : ∀ {a b} {A : Set a} {B : A → Set b} {u v : Σ A B}
           → (s : u ≡ v) → transport B (ap fst s) (snd u) ≡ snd v
  snd-path refl = refl

  cancel-left : ∀ {a} {A : Set a} {x y z : A} (p : x ≡ y) (q : x ≡ z)
              → p ∙ (sym p ∙ q) ≡ q
  cancel-left refl q = refl

  right-inverse : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → p ∙ sym p ≡ refl
  right-inverse refl = refl

module TotalForm
  {@♭ ℓ : Level}
  (@♭ Γ Γ′ : Set ℓ)
  (@♭ Γ-discrete : Discrete Γ)
  (@♭ Γ′-discrete : Discrete Γ′)
  (@♭ A : Γ → Set ℓ)
  (@♭ f : Γ′ → Γ)
  (@♭ shaped : RelativeShapeOver Γ Γ-discrete A)
  (@♭ reshaped : RelativeShapeOver Γ′ Γ′-discrete (A ∘ f)) where

  open Comparison Γ Γ′ Γ-discrete Γ′-discrete A f shaped reshaped public

  -- The conclusion in total form. A type of evidence, not an assumption.
  TotalComparisonIsEquivalence : Set ℓ
  TotalComparisonIsEquivalence = IsEquiv comparison-total

  private
    T′ : Set ℓ
    T′ = Output.Total reshaped

    tri : (z : T′) → fst (comparison-total z) ≡ Output.projection reshaped z
    tri = triangle comparison-over

  ----------------------------------------------------------------------
  -- Fibre form ⇒ total form.

  module FromFibres (E : ComparisonIsEquivalence) where

    private
      inv : PulledTotal → T′
      inv w = fst (inverse (E (fst w)) (snd w))

      sec : (w : PulledTotal) → comparison-total (inv w) ≡ w
      sec w = Σ-path {B = PulledFamily}
        (tri (fst v) ∙ snd v) (section (E (fst w)) (snd w))
        where
        v : Output.family reshaped (fst w)
        v = inverse (E (fst w)) (snd w)

      ret : (z : T′) → inv (comparison-total z) ≡ z
      ret z = ap fst
        ( ap (inverse (E γ)) (sym at-z)
        ∙ retraction (E γ) (z , sym (tri z)) )
        where
        γ : Γ′
        γ = fst (comparison-total z)

        at-z : comparison γ (z , sym (tri z)) ≡ snd (comparison-total z)
        at-z = ap (λ r → transport PulledFamily r (snd (comparison-total z)))
                  (right-inverse (tri z))

    total : TotalComparisonIsEquivalence
    total = quasi-inverse inv sec ret

  ----------------------------------------------------------------------
  -- Total form ⇒ fibre form, over a set.

  module FromTotal (Γ′-set : IsSet Γ′) (E : TotalComparisonIsEquivalence) where

    private
      module At (γ′ : Γ′) where

        inv : PulledFamily γ′ → Output.family reshaped γ′
        inv x = inverse E (γ′ , x) ,
                (sym (tri (inverse E (γ′ , x))) ∙ ap fst (section E (γ′ , x)))

        sec : (x : PulledFamily γ′) → comparison γ′ (inv x) ≡ x
        sec x =
          ap (λ r → transport PulledFamily r (snd (comparison-total z)))
             (cancel-left (tri z) (ap fst s))
          ∙ snd-path {B = PulledFamily} s
          where
          z : T′
          z = inverse E (γ′ , x)

          s : comparison-total z ≡ (γ′ , x)
          s = section E (γ′ , x)

        ret : (w : Output.family reshaped γ′) → inv (comparison γ′ w) ≡ w
        ret w = fiber-path
          ( ap (inverse E)
               (sym (Σ-path {B = PulledFamily} (tri (fst w) ∙ snd w) refl))
          ∙ retraction E (fst w) )
          (Γ′-set _ _ _ _)

    fibres : ComparisonIsEquivalence
    fibres γ′ = quasi-inverse (At.inv γ′) (At.sec γ′) (At.ret γ′)
