Adapted for the Orbifolds library by Claude Opus 5.5, an AI model made by
Anthropic, prompted by Colin Zwanziger, 12 November 2026 (local time),
at orbifold gate H9, with Astra's release of 13 November 2026 (UTC). The
source is Claude Fable 5.2's scratch check LemmasABAgainstModalities.lagda
(SHA-256
c29d1be120dfa38fd8815cdebe80063fb653da2f6e6955b08a8fec4850736839), in
provenance/companions/orbifolds-h9-universe-2026-11-13.zip, code of
this project. Changes: the module name (gist.Scratch to gist.Orbifolds)
and the imports of the other adapted modules; the proofs are unchanged.
The original text follows. The two audits that it names are
references/A18-h9-universe-interface-audit.txt and
references/A15-h9-followup-audit.txt, the note is
references/F19-h9-universe-convention.md, and the snapshot is an
earlier local delivery, which the package does not include.

Claude (Fable), 13 November 2026.

A scratch check of Lemmas A and B of the orbifolds roadmap (Section 3.9,
gate H9) against the existing interfaces of the Orbifolds library, with the
universe convention of Astra's audits `h9-universe-interface-audit.txt` and
`fable-h9-followup-audit.txt`.

It is NOT part of the formalization.  It backs the note
`fable-confirm-orbifolds-h9-universe-convention-2026-11-13.md`.  Opus owns
the implementation and may use or ignore it.

Checked against unmodified copies of `gist.Orbifolds.Modalities` and
`gist.Orbifolds.Nullification` from the snapshot
`orbifolds-agda-statement-layer-2026-11-12`.

The convention, in the form with a spare universe.  The carrier X is in 𝓦.
The modality is on the universe (𝓦 ⊔ 𝓣) ⁺, for an arbitrary 𝓣, and is the
nullification at pointed generators B i.  The classifier is the type
Ω¬¬ (𝓦 ⊔ 𝓣) of ¬¬-stable propositions, which lives in the universe of the
modality.  Only the existing recursor ○-rec of that one universe is used.

Hypotheses beyond the interface:

  pe : propositional extensionality at 𝓦 ⊔ 𝓣 (ordinary);
  κ  : every point of a generator is ¬¬-equal to its base point (what
       `SmoothLine.points-of-spectra-are-infinitesimal` gives under
       Postulate K, transported along lift).

Results:

  Ω¬¬-is-modal
  lemma-A : η (lift x) ＝ η (lift y) → ¬¬ (x ＝ y)
  lemma-B.inclusions-of-stable-subtypes-are-étale

In Lemma B the predicate takes values in the universe of the modality.

No external code is used or adapted.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse

module gist.Orbifolds.LemmasAB
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {𝓦 𝓣 𝓟 : Universe}
        (pe : propext (𝓦 ⊔ 𝓣))
        (P : subuniverse ((𝓦 ⊔ 𝓣) ⁺) 𝓟)
        (P-is-reflective : subuniverse-is-reflective P)
        (P-is-sigma-closed : subuniverse-is-sigma-closed P)
        (P-is-replete : subuniverse-is-replete P)
        {I : 𝓤₀ ̇ }
        (B : I → (𝓦 ⊔ 𝓣) ⁺ ̇ )
        (b : (i : I) → B i)
       where

open import UF.Embeddings
open import UF.Equiv
open import UF.Subsingletons-FunExt
open import UF.UniverseEmbedding using (Lift ; lift ; lower)

open import Modal.ReflectiveSubuniverse P P-is-reflective

open import gist.CohesiveApartness.Flat
 using (is-null ; null-iff-maps-are-constant)
open import gist.Orbifolds.Modalities fe pt P
             P-is-reflective P-is-sigma-closed P-is-replete
 using (is-étale ; étale-from-modal-family)
open import gist.Orbifolds.Nullification fe
 using (is-nullification ; propositions-are-modal)
open import gist.Orbifolds.StableClassifier
 using (Ω¬¬ ; module classifier)

open PropositionalTruncation pt

private
 𝓜 : Universe
 𝓜 = (𝓦 ⊔ 𝓣) ⁺

module _ (ν : is-nullification B b P)
         (κ : (i : I) (v : B i) → ¬¬ (v ＝ b i))
       where

 open classifier fe pe

 Ω¬¬-is-modal : is-modal (Ω¬¬ (𝓦 ⊔ 𝓣))
 Ω¬¬-is-modal =
  rl-implication (ν (Ω¬¬ (𝓦 ⊔ 𝓣)))
   (λ i → rl-implication
           (null-iff-maps-are-constant fe (B i) (b i) (Ω¬¬ (𝓦 ⊔ 𝓣)))
           (maps-into-Ω¬¬-are-constant (b i) (κ i)))

 module _ {X : 𝓦 ̇ } where

  X̄ : 𝓜 ̇
  X̄ = Lift 𝓜 X

  classify : X → X̄ → Ω¬¬ (𝓦 ⊔ 𝓣)
  classify x z = Lift 𝓣 (¬¬ (x ＝ lower z)) ,
                 ×-is-prop (negations-are-props fe) 𝟙-is-prop ,
                 (λ φ → lift 𝓣 (three-negations-imply-one (¬¬-functor lower φ)))

  lemma-A : (x y : X) → η X̄ (lift 𝓜 x) ＝ η X̄ (lift 𝓜 y) → ¬¬ (x ＝ y)
  lemma-A x y e = lower III
   where
    c : ○ X̄ → Ω¬¬ (𝓦 ⊔ 𝓣)
    c = ○-rec X̄ (Ω¬¬ (𝓦 ⊔ 𝓣)) Ω¬¬-is-modal (classify x)

    β : (z : X̄) → c (η X̄ z) ＝ classify x z
    β = ○-rec-compute X̄ (Ω¬¬ (𝓦 ⊔ 𝓣)) Ω¬¬-is-modal (classify x)

    I₀ : pr₁ (c (η X̄ (lift 𝓜 x)))
    I₀ = transport pr₁ ((β (lift 𝓜 x)) ⁻¹) (lift 𝓣 (¬¬-intro refl))

    II : pr₁ (c (η X̄ (lift 𝓜 y)))
    II = transport (λ w → pr₁ (c w)) e I₀

    III : Lift 𝓣 (¬¬ (x ＝ y))
    III = transport pr₁ (β (lift 𝓜 y)) II

  module lemma-B
          (S : X → 𝓜 ̇ )
          (S-is-prop-valued : (x : X) → is-prop (S x))
          (S-is-stable : (x y : X) → S x → ¬¬ (x ＝ y) → S y)
         where

   S̄ : 𝓜 ̇
   S̄ = Σ z ꞉ X̄ , S (lower z)

   j : S̄ → X̄
   j = pr₁

   E : ○ X̄ → 𝓜 ̇
   E w = ∥ (Σ s ꞉ S̄ , η X̄ (j s) ＝ w) ∥

   E-is-modal : (w : ○ X̄) → is-modal (E w)
   E-is-modal w = propositions-are-modal B b P ν (E w) ∥∥-is-prop

   j-is-embedding : is-embedding j
   j-is-embedding = pr₁-is-embedding (λ z → S-is-prop-valued (lower z))

   fibre-to-E : (z : X̄) → fiber j z → E (η X̄ z)
   fibre-to-E z (s , p) = ∣ s , ap (η X̄) p ∣

   E-to-fibre : (z : X̄) → E (η X̄ z) → fiber j z
   E-to-fibre z t = (z , m) , refl
    where
     γ : (Σ s ꞉ S̄ , η X̄ (j s) ＝ η X̄ z) → S (lower z)
     γ ((z' , m') , q) =
      S-is-stable (lower z') (lower z) m' (lemma-A (lower z') (lower z) q)

     m : S (lower z)
     m = ∥∥-rec (S-is-prop-valued (lower z)) γ t

   inclusions-of-stable-subtypes-are-étale : is-étale j
   inclusions-of-stable-subtypes-are-étale =
    étale-from-modal-family j E E-is-modal
     (λ z → logically-equivalent-props-are-equivalent
             (j-is-embedding z) ∥∥-is-prop (fibre-to-E z) (E-to-fibre z))

\end{code}
