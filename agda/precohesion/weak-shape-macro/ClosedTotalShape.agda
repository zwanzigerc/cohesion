{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE TRANCHE R, statement R4: the shape of a closed total.
-- Opus, 14 November 2026; opus-closed-limits-01 (delta 02), implementing
-- FABLE-PLAN-SET-SOURCE-TRANCHE-R-01 section 3.8 against Fable's UNCHANGED
-- SetSourceReflectionStatements.ClosedTotal.
--
-- Telescope exactly ClosedTotal's, all crisp: levels i b; Q, E, T, P,
-- P-prop, dP at level i ⊔ b (the crisp AtSupport adapter is used HERE ONLY,
-- as the release asks); W : Set i; sW : ShapeData W; cert : LargeOn b sW;
-- fe : FunExt₂ i (i ⊔ b). With cη = c-map (λ r → raise (η sW (lower r))):
--   recursor : R4-Recursor    for crisp D (discrete set at i ⊔ b) and crisp
--              g : cP W → D: CoconeP.extendP of r₀ = recLarge (g ∘ unitP)
--              and m = g ∘ pointP, with the agreement r₀ z ≡ m p obtained by
--              discrete-elim dP on p, the ORDINARY binder z kept inside the
--              motive, and At.recLarge-unique fe at a crisp p;
--   computes : R4-Computes recursor   generatorsP-unique on cP W: cη-unit,
--              extendP-unit, recLarge-η at unitP; cη-point, extendP-point
--              at pointP;
--   unique   : R4-Unique      generatorsP-unique on cP (ʃ sW): large
--              uniqueness on old units, the supplied homotopy at pointP;
--   closed-shape : ShapeData (cP W) = Assembled.closed-shape, carrier
--              cP (ʃ sW) and unit cη by refl.
-- The only extensionality is the crisp mixed FunExt₂ i (i ⊔ b), inside
-- At.recLarge-unique. No shape stability, effectivity, continuity or
-- declaration. Nothing is postulated.
module ClosedTotalShape where

open import Foundations
open import CaptureContext using (Raise; raise; lower)
open import GlobalPrecohesion using (ShapeData; ʃ; η; discrete-elim)
open import GlobalPropositions using (FunExt₂)
open import LargeTarget using (LargeOn; module At)
open import OrdinaryTruncation using (PropTruncation; own-level)
open import SmallQuotient using (Quotients; Eliminates)
open import ClosedReflectionRaised using (module AtSupport)
open import SetSourceReflectionStatements using (module ClosedTotal)

module R4 {@♭ i b : Level} (@♭ Q : Quotients (i ⊔ b))
  (@♭ E : Eliminates Q (i ⊔ b)) (@♭ T : PropTruncation (i ⊔ b))
  (@♭ P : Set (i ⊔ b)) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  {@♭ W : Set i} (@♭ sW : ShapeData W) (@♭ cert : LargeOn b sW)
  (@♭ fe : FunExt₂ i (i ⊔ b)) where

  open ClosedTotal {i} {b} Q E T P P-prop dP sW cert fe
    using (cη; cη-unit; cη-point; R4-Recursor; R4-Computes; R4-Unique;
           module Assembled)
  open AtSupport {i} {b} Q E T P P-prop dP
    using (cP; unitP; pointP; glueP; module CoconeP; generatorsP-unique)

  -- The recursor at a crisp discrete target D and a crisp g.
  module Rec (@♭ D : Set (i ⊔ b)) (@♭ D-set : IsSet D)
    (@♭ D-discrete : Discrete D) (@♭ g : cP W → D) where

    private
      module A = At b cert D D-set D-discrete

    r₀ : ʃ sW → D
    r₀ = A.recLarge (λ w → g (unitP w))

    r₀-η : (w : W) → r₀ (η sW w) ≡ g (unitP w)
    r₀-η = A.recLarge-η (λ w → g (unitP w))

    m : P → D
    m p = g (pointP p)

    -- On a crisp point of the support: large uniqueness, all three
    -- arguments crisp; the ordinary z is bound only afterwards.
    agreement-at : (@♭ p : P) → (z : ʃ sW) → r₀ z ≡ m p
    agreement-at p = A.recLarge-unique fe r₀ (λ _ → m p)
      (λ w → r₀-η w ∙ ap g (glueP w p))

    agreement : (z : ʃ sW) (p : P) → r₀ z ≡ m p
    agreement z p =
      discrete-elim dP (λ p′ → (z′ : ʃ sW) → r₀ z′ ≡ m p′) agreement-at p z

    private
      module X = CoconeP {W = ʃ sW} E (own-level T) D-set r₀ m agreement

    rec : cP (ʃ sW) → D
    rec = X.extendP

    rec-unit : (s : ʃ sW) → rec (unitP s) ≡ r₀ s
    rec-unit = X.extendP-unit

    rec-point : (p : P) → rec (pointP p) ≡ m p
    rec-point = X.extendP-point

    rec-computes : (z : cP W) → rec (cη z) ≡ g z
    rec-computes = generatorsP-unique E D-set (λ z → rec (cη z)) g
      (λ w → ap rec (cη-unit w) ∙ rec-unit (η sW w) ∙ r₀-η w)
      (λ p → ap rec (cη-point p) ∙ rec-point p)

  recursor : R4-Recursor
  recursor D D-set D-discrete g = Rec.rec D D-set D-discrete g

  computes : R4-Computes recursor
  computes D D-set D-discrete g = Rec.rec-computes D D-set D-discrete g

  unique : R4-Unique
  unique D D-set D-discrete k k′ e =
    generatorsP-unique E D-set k k′
      (λ s → At.recLarge-unique b cert D D-set D-discrete fe
               (λ s′ → k (unitP s′)) (λ s′ → k′ (unitP s′))
               (λ w → ap k (sym (cη-unit w)) ∙ e (unitP w) ∙ ap k′ (cη-unit w))
               s)
      (λ p → ap k (sym (cη-point p)) ∙ e (pointP p) ∙ ap k′ (cη-point p))

  -- The shape datum of the closed total.
  open Assembled recursor computes unique
    using (closed-shape; carrier-is; unit-is) public
