{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Importing client of Fable's UNCHANGED SetSourceReflectionStatements.
-- Opus, 14 November 2026; opus-closed-limits-01 (delta 02).
-- Nothing is postulated and nothing is declared.
--
-- Every Statement-… type of the probe is inhabited, written through the
-- PROBE'S OWN modules (Gluing, Gluing.Pullback, AtLevel, AtLevel.PullbackP,
-- ClosedTotal), with the proofs of SetSourceReflection and ClosedTotalShape;
-- likewise the three fields of R4, and Assembled.closed-shape with its
-- actual carrier cP (ʃ sW) and unit cη (refl).
module SetSourceReflectionClient where

open import Foundations
open import GlobalPrecohesion using (ShapeData; ʃ; η)
open import GlobalPropositions using (FunExt₂)
open import LargeTarget using (LargeOn)
open import OrdinaryTruncation using (PropTruncation)
open import SmallQuotient using (Quotients; Eliminates)
open import SetSourceReflectionStatements
  using (module Gluing; module AtLevel; module ClosedTotal)
open import ClosedReflectionRaised using (module AtSupport)
open import SetSourceReflection using (module RGluing; module RAtLevel)
open import ClosedTotalShape using (module R4)

------------------------------------------------------------------------
-- R1, R2, R3 at one level; ordinary parameters.

module AtOneLevel {ℓ : Level} (Q : Quotients ℓ) (E : Eliminates Q ℓ)
  (T : PropTruncation ℓ) (P : Set ℓ) (P-prop : IsProp P) where

  private
    module S = Gluing Q E T P P-prop
    module G = RGluing Q E T P P-prop

  r1 : {X Y Z : Set ℓ} (f : X → Z) (g : Y → Z) → S.Pullback.Statement-R1 f g
  r1 f g = G.R1.R1 f g

  r2 : S.Statement-R2
  r2 = G.R2

  r3 : S.Statement-R3
  r3 = G.R3

------------------------------------------------------------------------
-- R1P, R2P, R3P; only the levels crisp, no discreteness of P.

module AtLevels {@♭ i b : Level} (Q : Quotients (i ⊔ b))
  (E : Eliminates Q (i ⊔ b)) (T : PropTruncation (i ⊔ b))
  (P : Set (i ⊔ b)) (P-prop : IsProp P) where

  private
    module S = AtLevel {i} {b} Q E T P P-prop
    module G = RAtLevel {i} {b} Q E T P P-prop

  r1P : {V₁ V₂ V₀ : Set i} (f : V₁ → V₀) (g : V₂ → V₀)
      → S.PullbackP.Statement-R1P f g
  r1P f g = G.R1P.R1P f g

  r2P : S.Statement-R2P
  r2P = G.R2P

  r3P : S.Statement-R3P
  r3P = G.R3P

------------------------------------------------------------------------
-- R4 and the shape of a closed total.

module ClosedTotalClient {@♭ i b : Level} (@♭ Q : Quotients (i ⊔ b))
  (@♭ E : Eliminates Q (i ⊔ b)) (@♭ T : PropTruncation (i ⊔ b))
  (@♭ P : Set (i ⊔ b)) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  {@♭ W : Set i} (@♭ sW : ShapeData W) (@♭ cert : LargeOn b sW)
  (@♭ fe : FunExt₂ i (i ⊔ b)) where

  private
    module S = ClosedTotal {i} {b} Q E T P P-prop dP sW cert fe
    module R = R4 {i} {b} Q E T P P-prop dP sW cert fe
    module A = AtSupport {i} {b} Q E T P P-prop dP

  recursor : S.R4-Recursor
  recursor = R.recursor

  computes : S.R4-Computes recursor
  computes = R.computes

  unique : S.R4-Unique
  unique = R.unique

  closed-shape : ShapeData (A.cP W)
  closed-shape = S.Assembled.closed-shape recursor computes unique

  carrier : ʃ closed-shape ≡ A.cP (ʃ sW)
  carrier = refl

  unit : (z : A.cP W) → η closed-shape z ≡ S.cη z
  unit z = refl
