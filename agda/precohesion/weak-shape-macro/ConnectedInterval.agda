{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE CONNECTED-INTERVAL THEOREM for T = Shape0 ∘ ♯ (paper Lemma 3.4,
-- after Lawvere–Menni 2015, Lemma 6.2, by the selector proof).
-- Opus, 13 November 2026; opus-connected-interval-01, implementing
-- CONNECTED-INTERVAL-PLAN-FABLE-01.txt section 4 as released by
-- CONNECTED-INTERVAL-PLAN-ASTRA-02.txt.
--
-- Statement. Fix a crisp level ℓ and a crisp type A : Set ℓ, and write
--     X = ♯ A,   J = ♯ (Two ℓ),   Z = X × X,   W = Z × J.
-- Given crisp shape data sX sJ sZ sW for these four types and a CRISP proof
-- pW that  compare sZ sJ sW : ʃ sW → ʃ sZ × ʃ sJ  is an equivalence, and
-- given ORDINARY proofs pZ that  compare sX sX sZ  is an equivalence and c
-- that ʃ sJ is contractible:
--     shape-is-prop           : IsProp (ʃ sX)
--     inhabited-contractible  : Merely A → IsContr (ʃ sX)
-- the latter via the actual coaugmentation  A → ♯ A → ʃ sX.
--
-- Reading. For the paper, A is a discrete base object and ʃ (♯ A) is
-- Π₀∇A. For an arbitrary crisp A the statement is about the codiscrete
-- object ♯ A (semantically ∇ΓA); no claim is made that every native A is a
-- base object. ShapeData is SET-target shape data (Shape0): this is not the
-- full-shape (Π∇) theorem, although the selector lemma used is higher.
--
-- What is NOT claimed. No converse and no emptiness statement: without the
-- Nullstellensatz ʃ (♯ A) may be contractible for empty A. Without Merely A
-- only IsProp is obtained (see ConnectedSelector.control).
--
-- What is used. The shape data rec / rec-η / unique and the canonical
-- product comparisons compare / compare-η of GlobalPrecohesion, the native
-- sharp adapter (ConnectedIntervalNative) and the elementary selector
-- (ConnectedSelector). `unique` is applied exactly twice, to maps
-- ʃ sZ → ʃ sX, and yields the endpoint laws at EVERY shape element: no
-- surjectivity of η and no induction on shape elements. No function
-- extensionality, Nullstellensatz, continuity (Continuous, EpiC, MonoC),
-- stability, choice, large-target certificate, classifier or capture macro.
-- GlobalPrecohesion also DEFINES the Nullstellensatz and continuity
-- predicates; they are excluded by the explicit import list below and no
-- witness of them occurs (CONNECTED-INTERVAL-PLAN-ASTRA-02, clarification).
-- Merely A is eliminated only into the ℓ-small proposition ʃ sX.
--
-- Crispness (plan 4.3). `unique` takes its two maps and their agreement on
-- units crisply; those mention A, the four shapes and, through the inverse
-- of pW, pW itself. So these six are crisp module parameters. pZ enters
-- only at ordinary u v after the crisp equalities exist, and c only for the
-- endpoint path: both are ordinary parameters of the submodule Conclusion.
-- With pW ordinary the module is rejected (ConnectedIntervalOrdinaryW).
--
-- Not --safe, and no such claim: ShapeData has crisp constructor fields and
-- GlobalPrecohesion uses --flat-split. Nothing is postulated here.
module ConnectedInterval where

open import Foundations
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion
  using ( ShapeData; ʃ; ʃ-set; ʃ-discrete; η; rec; rec-η; unique
        ; first; second; compare; compare-η; PreservesProduct; Merely )
open import ConnectedSelector using (selector)
open import ConnectedIntervalNative using (Two; i₀; i₁; m; m-left; m-right)

module Modal {@♭ ℓ : Level} (@♭ A : Set ℓ)
  -- four selected shapes, all at level ℓ
  (@♭ sX : ShapeData (♯ A))
  (@♭ sJ : ShapeData (♯ (Two ℓ)))
  (@♭ sZ : ShapeData (♯ A × ♯ A))
  (@♭ sW : ShapeData ((♯ A × ♯ A) × ♯ (Two ℓ)))
  -- the product certificate whose INVERSE occurs in maps given to `unique`
  (@♭ pW : PreservesProduct sZ sJ sW)
  where

  ----------------------------------------------------------------------
  -- Steps 1–7: definitions from the crisp parameters only.

  -- 1. The inverse of the comparison for W = Z × J.
  rW : ʃ sZ × ʃ sJ → ʃ sW
  rW = inverse pW

  -- 2. The two distinguished points of ʃ sJ.
  b₀ b₁ : ʃ sJ
  b₀ = η sJ i₀
  b₁ = η sJ i₁

  -- 3. The selector, pushed through the shape of W.
  m# : ʃ sW → ʃ sX
  m# = rec sW (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ w → η sX (m w))

  m#-η : (w : (♯ A × ♯ A) × ♯ (Two ℓ)) → m# (η sW w) ≡ η sX (m w)
  m#-η = rec-η sW (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ w → η sX (m w))

  -- 4. The inverse comparison sends a pair of units to the unit of the pair.
  back-to-unit : (x : ♯ A × ♯ A) (i : ♯ (Two ℓ))
               → rW (η sZ x , η sJ i) ≡ η sW (x , i)
  back-to-unit x i =
    sym (ap rW (compare-η sZ sJ sW x i)) ∙ retraction pW (η sW (x , i))

  -- 5. The two pairs of maps ʃ sZ → ʃ sX to be compared.
  f₀ f₁ : ʃ sZ → ʃ sX
  f₀ z = m# (rW (z , b₀))
  f₁ z = m# (rW (z , b₁))

  g₀ g₁ : ʃ sZ → ʃ sX
  g₀ = first sX sX sZ
  g₁ = second sX sX sZ

  -- 6. Agreement on units.
  on-units₀ : (x : ♯ A × ♯ A) → f₀ (η sZ x) ≡ g₀ (η sZ x)
  on-units₀ x =
      ap m# (back-to-unit x i₀)
    ∙ m#-η (x , i₀)
    ∙ ap (η sX) (m-left x)
    ∙ sym (rec-η sZ (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ p → η sX (fst p)) x)

  on-units₁ : (x : ♯ A × ♯ A) → f₁ (η sZ x) ≡ g₁ (η sZ x)
  on-units₁ x =
      ap m# (back-to-unit x i₁)
    ∙ m#-η (x , i₁)
    ∙ ap (η sX) (m-right x)
    ∙ sym (rec-η sZ (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) (λ p → η sX (snd p)) x)

  -- 7. The two uses of uniqueness: agreement at EVERY z : ʃ sZ.
  everywhere₀ : (z : ʃ sZ) → f₀ z ≡ g₀ z
  everywhere₀ = unique sZ (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) f₀ g₀ on-units₀

  everywhere₁ : (z : ʃ sZ) → f₁ z ≡ g₁ z
  everywhere₁ = unique sZ (ʃ sX) (ʃ-set sX) (ʃ-discrete sX) f₁ g₁ on-units₁

  -- 12a. The coaugmentation A → ♯ A → ʃ sX (crisp data only; as in the
  -- audited ConnectedIntervalSignatureProbe it is declared in Modal).
  coaugmentation : A → ʃ sX
  coaugmentation a = η sX (sharp-unit a)

  ----------------------------------------------------------------------
  -- Steps 8–12: the ordinary hypotheses enter only here.

  module Conclusion (pZ : PreservesProduct sX sX sZ)
                    (c : IsContr (ʃ sJ)) where

    -- 8.
    rZ : ʃ sX × ʃ sX → ʃ sZ
    rZ = inverse pZ

    h : ʃ sX → ʃ sX → ʃ sJ → ʃ sX
    h u v t = m# (rW (rZ (u , v) , t))

    -- 9. The endpoint laws for ALL u v : ʃ sX.
    L₀ : (u v : ʃ sX) → h u v b₀ ≡ u
    L₀ u v = everywhere₀ (rZ (u , v)) ∙ ap fst (section pZ (u , v))

    L₁ : (u v : ʃ sX) → h u v b₁ ≡ v
    L₁ u v = everywhere₁ (rZ (u , v)) ∙ ap snd (section pZ (u , v))

    -- 10. The connected interval supplies the endpoint path.
    endpoints : b₀ ≡ b₁
    endpoints = sym (snd c b₀) ∙ snd c b₁

    -- 11. T A is a proposition.
    shape-is-prop : IsProp (ʃ sX)
    shape-is-prop = selector h b₀ b₁ endpoints L₀ L₁

    -- 12b. If A is merely inhabited, T A is contractible. Merely A is
    -- eliminated into the ℓ-small proposition ʃ sX only; IsContr is built
    -- by pairing, so no extensionality is needed.
    inhabited-contractible : Merely A → IsContr (ʃ sX)
    inhabited-contractible mA = centre , shape-is-prop centre
      where
      centre : ʃ sX
      centre = mA (ʃ sX) shape-is-prop coaugmentation

  ----------------------------------------------------------------------
  -- The audited statements of ConnectedIntervalSignatureProbe, inhabited.

  ShapeIsProp : Set ℓ
  ShapeIsProp = PreservesProduct sX sX sZ → IsContr (ʃ sJ) → IsProp (ʃ sX)

  InhabitedContractible : Set (lsuc ℓ)
  InhabitedContractible =
    PreservesProduct sX sX sZ → IsContr (ʃ sJ) → Merely A → IsContr (ʃ sX)

  shape-is-prop-as-stated : ShapeIsProp
  shape-is-prop-as-stated pZ c = Conclusion.shape-is-prop pZ c

  inhabited-contractible-as-stated : InhabitedContractible
  inhabited-contractible-as-stated pZ c = Conclusion.inhabited-contractible pZ c
