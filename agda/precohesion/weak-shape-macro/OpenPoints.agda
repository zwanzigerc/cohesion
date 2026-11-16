{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGE O1: under the support, points-to-pieces of a set is an
-- equivalence. Opus, 14 November 2026; opus-closed-limits-01 (delta 03),
-- implementing FABLE-PLAN-SET-SOURCE-01 §4.1 (OPEN-QUALITY-AND-COMPARISON-
-- NATIVE-ROUTE-01, part 1), released by SET-SOURCE-PLAN-ASTRA-RELEASE-01.
--
-- Generic in its data (plan §2, design rule): crisp level i; the support
-- data sO, sQ, fe-i, pe-i, fe-j of PrincipalFilter.Principal sO … Quantified
-- (which define P and lower-bound); a crisp SET Z of level i with shape sZ;
-- choices sa on ♯ (♭ Z), saa on its square, and caa : LargeOn j saa.
--
--   o1 : PreservesProduct sa sa saa → Nullstellensatz sZ
--      → P → IsEquiv (points-to-pieces sZ)
--
-- All three hypotheses are ORDINARY. Steps (plan §4.1): ♭ Z is a discrete
-- set; m = rec sZ at z ↦ η sa (flat-sharp-unit z), with m (θ u) ≡ η sa (♯ u);
-- δ = χ of the diagonal of ♭ Z (MonoClassifier.Classification fe-i pe-i),
-- g (s , t) .ε = δ (s .ε , t .ε); n = At.recLarge of caa at η sO ∘ g
-- (certificate needed: ʃ sO is of level j; no large uniqueness). Under p,
-- θ a ≡ θ b gives, through m, the injectivity of compare (retraction of the
-- product law), n, its unit law and the truth square, e₀ (δ (a , b)) ≡
-- e₀ top; so (δ (a , b) , _) is a point of F and lower-bound p decodes it
-- to a ≡ b. Fibres of θ are then propositions, and the Nullstellensatz is
-- eliminated into the fibre itself (level i). No shape of anything built
-- from P; Merely is never eliminated into a larger universe.
module OpenPoints where

open import Foundations
open import NativeSharp using (♯; ε; sharp-unit; flat-sharp-unit)
open import FlatContext using (flat-discrete)
open import NativeFlatIdentity using (flat-set)
open import ShapeElim using (module SigmaDiscrete)
open import GlobalChoice using (×-set)
open import SmallPropositions using (PropExt; subtype-path; injective-fibres)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; points-to-pieces;
         Nullstellensatz; PreservesProduct; compare; compare-η)
open import GlobalPropositions using (FunExt₂)
open import LargeTarget using (LargeOn; module At)
open import BaseClassifier using (O; El; top)
open import MonoClassifier using (module Classification)
open import PrincipalFilter using (module Principal)
open import ClosedLimits using (inhabited-prop-equiv)

module O1 {@♭ i : Level} (@♭ sO : ShapeData (♯ (O i)))
  (@♭ sQ : ShapeData (Principal.Q sO))
  (@♭ fe-i : FunExt₂ i i) (@♭ pe-i : PropExt i)
  (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  {@♭ Z : Set i} (@♭ Z-set : IsSet Z) (@♭ sZ : ShapeData Z)
  (@♭ sa : ShapeData (♯ (♭ Z)))
  (@♭ saa : ShapeData (♯ (♭ Z) × ♯ (♭ Z)))
  (@♭ caa : LargeOn (lsuc i) saa) where

  open Principal sO using (P; e₀; F)
  module Qd = Principal.Quantified sO sQ fe-i pe-i fe-j

  θ : ♭ Z → ʃ sZ
  θ = points-to-pieces sZ

  -- 1. ♭ Z is a discrete set; so is its square.
  A♭ : Set i
  A♭ = ♭ Z

  A♭-set : IsSet A♭
  A♭-set = flat-set Z-set

  A♭-discrete : Discrete A♭
  A♭-discrete = flat-discrete Z

  AA-discrete : Discrete (A♭ × A♭)
  AA-discrete = SigmaDiscrete.discrete A♭-discrete (λ _ → A♭-discrete)

  -- 2. m and its value on points.
  m : ʃ sZ → ʃ sa
  m = rec sZ (ʃ sa) (ʃ-set sa) (ʃ-discrete sa) (λ z → η sa (flat-sharp-unit z))

  m-θ : (u : A♭) → m (θ u) ≡ η sa (sharp-unit u)
  m-θ (box z) =
    rec-η sZ (ʃ sa) (ʃ-set sa) (ʃ-discrete sa) (λ z′ → η sa (flat-sharp-unit z′)) z

  -- 3. The characteristic map of the diagonal of ♭ Z.
  diag : A♭ → A♭ × A♭
  diag a = a , a

  diag-mono : (w : A♭ × A♭) → IsProp (Fiber diag w)
  diag-mono w (x , q) (y , r) =
    subtype-path (λ z → ×-set A♭-set A♭-set (diag z) w)
      (ap fst q ∙ sym (ap fst r))

  module Ch = Classification fe-i pe-i AA-discrete A♭-discrete diag diag-mono

  δ : A♭ × A♭ → O i
  δ = Ch.χ

  -- 4. g on the sharp square.
  g : ♯ A♭ × ♯ A♭ → ♯ (O i)
  g w .ε = δ (fst w .ε , snd w .ε)

  -- 5. n, by the larger-target certificate.
  private
    module A = At (lsuc i) caa (ʃ sO) (ʃ-set sO) (ʃ-discrete sO)

  n : ʃ saa → ʃ sO
  n = A.recLarge (λ w → η sO (g w))

  n-η : (w : ♯ A♭ × ♯ A♭) → n (η saa w) ≡ η sO (g w)
  n-η = A.recLarge-η (λ w → η sO (g w))

  -- 6. Injectivity of θ under the support.
  module _ (pp : PreservesProduct sa sa saa) where

    compare-injective : {w w′ : ♯ A♭ × ♯ A♭}
      → compare sa sa saa (η saa w) ≡ compare sa sa saa (η saa w′)
      → η saa w ≡ η saa w′
    compare-injective {w} {w′} e =
      sym (retraction pp (η saa w)) ∙ ap (inverse pp) e ∙ retraction pp (η saa w′)

    θ-injective : P → (a b : A♭) → θ a ≡ θ b → a ≡ b
    θ-injective p a b e = sym (ap fst (snd fib)) ∙ ap snd (snd fib)
      where
      e₁ : η sa (sharp-unit a) ≡ η sa (sharp-unit b)
      e₁ = sym (m-θ a) ∙ ap m e ∙ m-θ b

      e₂ : η saa (sharp-unit a , sharp-unit b) ≡ η saa (sharp-unit a , sharp-unit a)
      e₂ = compare-injective
        (compare-η sa sa saa (sharp-unit a) (sharp-unit b)
         ∙ pair-path refl (sym e₁)
         ∙ sym (compare-η sa sa saa (sharp-unit a) (sharp-unit a)))

      e₃ : e₀ (δ (a , b)) ≡ e₀ (δ (a , a))
      e₃ = sym (n-η (sharp-unit a , sharp-unit b)) ∙ ap n e₂
           ∙ n-η (sharp-unit a , sharp-unit a)

      e₄ : e₀ (δ (a , b)) ≡ e₀ top
      e₄ = e₃ ∙ ap e₀ (Ch.truth-square a)

      holds : El (δ (a , b))
      holds = Qd.lower-bound p (δ (a , b) , e₄)

      fib : Fiber diag (a , b)
      fib = Ch.to-fibre (a , b) holds

    -- 7. The fibres are propositions; the Nullstellensatz fills them.
    o1 : Nullstellensatz sZ → P → IsEquiv θ
    o1 ns p = inhabited-prop-equiv fib-prop
      (λ z → ns z (Fiber θ z) (fib-prop z) (λ x → x))
      where
      fib-prop : (z : ʃ sZ) → IsProp (Fiber θ z)
      fib-prop = injective-fibres θ (ʃ-set sZ) (θ-injective p)

  -- The statement in the kernel's order of hypotheses.
  statement-O1 : PreservesProduct sa sa saa → Nullstellensatz sZ
               → P → IsEquiv (points-to-pieces sZ)
  statement-O1 pp = o1 pp
