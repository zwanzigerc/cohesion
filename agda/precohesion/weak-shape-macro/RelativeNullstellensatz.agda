{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The relative Nullstellensatz over a SET base, DERIVED. Postulate-free.
-- Claude (Fable), 13 November 2026; fable-impl-02, HANDOFF-04 item (d).
-- Part of the Nullstellensatz extension.
--
-- Let K be a whole-context reflection of A over a closed discrete set Γ.
--
--   relative-nullstellensatz   from the Nullstellensatz of ANY terminal
--       shape data t of the closed type Σ Γ A (for instance the bridged
--       data of a declared terminal instance) to  NAxiom K:  every element
--       of the total space of K merely comes from a crisp point of Σ Γ A.
--       Route: TotalBridge makes (Total K, unit K) terminal shape data of
--       Σ Γ A; the Nullstellensatz is independent of the choice of shape
--       data (GlobalChoice).
--   fibre-nullstellensatz      from NAxiom K to the statement at a crisp
--       point γ: every element of the fibre  family K γ  merely comes from
--       a crisp point of A γ.
--       Route: the witness is a crisp point (γ′ , a) with a path γ′ ≡ γ.
--       The identity type of a discrete type between crisp points is
--       discrete, so the path may be assumed crisp, and a crisp path
--       transports the crisp point a. Γ being a set makes the remaining
--       path in the fibre automatic.
--
-- No comparison of a fresh shape with a pulled-back one is inverted here.
--
-- Higher bases. NAxiom K is still true (FABLE-REVIEW-01 Proposition 3.2) and
-- still derivable from the terminal instance, by RELATIVE0-HIGHER-BASE-
-- RESEARCH-02 §3: TotalExistence shows that the SET TRUNCATION of Total K is
-- the terminal shape of Σ Γ A, and surjectivity is detected on set
-- truncations. That needs same-level set truncation with its path-space
-- theorem and its discreteness, none of which is in this tree. Until then a
-- relative instance over a higher base is declared
-- (NullstellensatzExtension.declareNullstellensatz), not derived.
module RelativeNullstellensatz where

open import Foundations
import RelativeSliceShape as R
open R using (RelativeShapeOver)
open import FlatContext using (fiber-path)
open import DiscretePullback using (identity-discrete)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import GlobalChoice using (transport-nullstellensatz)
open import TotalBridge using (module TotalData)
open import NullstellensatzExtension using (module Statement)

module _
  {@♭ ℓ : Level} (@♭ fe : FunExtAt ℓ)
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
  {@♭ A : Γ → Set ℓ} (@♭ K : RelativeShapeOver Γ dΓ A) where

  relative-nullstellensatz : (@♭ t : ShapeData (Σ Γ A)) → Nullstellensatz t
                           → Statement.NAxiom K
  relative-nullstellensatz t n =
    transport-nullstellensatz t (TotalData.total-data fe Γ-set K) n

module _
  {@♭ ℓ : Level}
  {@♭ Γ : Set ℓ} {@♭ dΓ : Discrete Γ} (@♭ Γ-set : IsSet Γ)
  {@♭ A : Γ → Set ℓ} (@♭ K : RelativeShapeOver Γ dΓ A) (@♭ γ : Γ) where

  private
    T = R.Output.Total K
    p = R.Output.projection K
    u = R.Output.unit K
    uo = R.Output.unit-over K

  -- A crisp point of the fibre over γ whose unit is the given element.
  FibrePoint : R.Output.family K γ → Set ℓ
  FibrePoint z = Σ (♭ (A γ)) (λ v → R.Output.family-unit K γ (counit v) ≡ z)

  private
    -- The witness lies over γ by a CRISP path.
    crisp-case : (@♭ γ′ : Γ) (@♭ a : A γ′) (@♭ w : γ′ ≡ γ)
               → (t : T) (e : p t ≡ γ) → u (γ′ , a) ≡ t → FibrePoint (t , e)
    crisp-case γ′ a refl t e q = box a , fiber-path q (Γ-set _ _ _ _)

    -- An arbitrary path between the two crisp points may be assumed crisp.
    any-case : (@♭ γ′ : Γ) (@♭ a : A γ′) → γ′ ≡ γ
             → (t : T) (e : p t ≡ γ) → u (γ′ , a) ≡ t → FibrePoint (t , e)
    any-case γ′ a = discrete-elim (identity-discrete dΓ γ′ γ)
      (λ _ → (t : T) (e : p t ≡ γ) → u (γ′ , a) ≡ t → FibrePoint (t , e))
      (λ w → crisp-case γ′ a w)

    from-point : (t : T) (e : p t ≡ γ) (v : ♭ (Σ Γ A)) → u (counit v) ≡ t
               → FibrePoint (t , e)
    from-point t e (box (γ′ , a)) q =
      any-case γ′ a (sym (uo (γ′ , a)) ∙ ap p q ∙ e) t e q

  fibre-nullstellensatz : Statement.NAxiom K
                        → (z : R.Output.family K γ) → Merely (FibrePoint z)
  fibre-nullstellensatz n z P P-prop k =
    n (fst z) P P-prop (λ w → k (from-point (fst z) (snd z) (fst w) (snd w)))
