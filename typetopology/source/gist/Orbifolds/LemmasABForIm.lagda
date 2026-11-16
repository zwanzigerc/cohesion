Adapted for the Orbifolds library by Claude Opus 5.5, an AI model made by
Anthropic, prompted by Colin Zwanziger, 12 November 2026 (local time),
at orbifold gate H9, with Astra's release of 13 November 2026 (UTC). The
source is Claude Fable 5.2's scratch check LemmasABForIm.lagda (SHA-256
9f4fb50949ee3bb20238bac07e8bcb230ee56c606d56e347ae043c7a3ae1f3a4), in
provenance/companions/orbifolds-h9-universe-2026-11-13.zip, code of
this project. Changes: the module name (gist.Scratch to gist.Orbifolds)
and the imports of the other adapted modules; the proofs are unchanged.
The original text follows; its references to the scratch modules now
mean StableClassifier and LemmasAB. The two audits that it names are
references/A18-h9-universe-interface-audit.txt and
references/A15-h9-followup-audit.txt, the note is
references/F19-h9-universe-convention.md, and the snapshot is an
earlier local delivery, which the package does not include.

Claude (Fable), 13 November 2026.

A scratch check: Lemmas A and B of the orbifolds roadmap (Section 3.9) for
the modality ℑ exactly as `gist.Orbifolds.Microlinearity` sets it up, with
the universe convention of Astra's audits `h9-universe-interface-audit.txt`
and `fable-h9-followup-audit.txt`:

  carriers in 𝓤 (or below);  one modality, on 𝓤 ⁺;  the generators
  `Lift (𝓤 ⁺) (Spec W)` of `Microlinearity`;  propositional extensionality
  at 𝓤 and Postulate K as ordinary hypotheses.

It is NOT part of the formalization.  It backs the note
`fable-confirm-orbifolds-h9-universe-convention-2026-11-13.md`.  Opus owns
the implementation and may use or ignore it.

Checked against unmodified copies of the modules of the snapshot
`orbifolds-agda-statement-layer-2026-11-12`.  The general statements are in
`gist.Scratch.LemmasABAgainstModalities`; here they are instantiated twice
against ONE subuniverse P on 𝓤 ⁺:

  for carriers in 𝓤   (the manifolds, G₀, G₁);
  for carriers in 𝓤₀  (the Euclidean spaces: the smooth line is in 𝓤₀).

Both instances use the classifier Ω¬¬ 𝓤 and the same reflector.  Nothing
relates reflections at two universes.

No external code is used or adapted.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.LemmasABForIm
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import UF.UniverseEmbedding using (Lift ; lift ; lower)
open import gist.CohesiveApartness.Flat using (♭ ; ♭-counit)

open smooth-line fe pt 𝓡
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
 using (ℑ-generator ; ℑ-generator-point)
open import gist.Orbifolds.Nullification fe
 using (is-nullification ;
        nullifications-are-Σ-closed ; nullifications-are-replete)

import gist.Orbifolds.LemmasAB as AB

module _ {𝓟 : Universe}
         (pe : propext 𝓤)
         (K : Postulate-K)
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  σ : subuniverse-is-sigma-closed P
  σ = nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν

  ρ : subuniverse-is-replete P
  ρ = nullifications-are-replete ℑ-generator ℑ-generator-point P ν

 open import Modal.ReflectiveSubuniverse P P-is-reflective using (○ ; η)
 open import gist.Orbifolds.Modalities fe pt P P-is-reflective σ ρ
  using (is-étale)

 points-of-generators-are-infinitesimal
  : (u : ♭ Weil-Presentation) (v : ℑ-generator u)
  → ¬¬ (v ＝ ℑ-generator-point u)
 points-of-generators-are-infinitesimal u v =
  ¬¬-functor (ap (lift (𝓤 ⁺)))
   (points-of-spectra-are-infinitesimal K (♭-counit u) (lower v))

 private
  κ = points-of-generators-are-infinitesimal

  module manifolds =
   AB fe pt {𝓤} {𝓤} {𝓟} pe P P-is-reflective σ ρ
      ℑ-generator ℑ-generator-point

  module Euclidean =
   AB fe pt {𝓤₀} {𝓤} {𝓟} pe P P-is-reflective σ ρ
      ℑ-generator ℑ-generator-point

 lemma-A-for-carriers-in-𝓤
  : {M : 𝓤 ̇ } (x y : M)
  → η (Lift (𝓤 ⁺) M) (lift (𝓤 ⁺) x) ＝ η (Lift (𝓤 ⁺) M) (lift (𝓤 ⁺) y)
  → ¬¬ (x ＝ y)
 lemma-A-for-carriers-in-𝓤 = manifolds.lemma-A ν κ

 lemma-A-for-carriers-in-𝓤₀
  : {V : 𝓤₀ ̇ } (x y : V)
  → η (Lift (𝓤 ⁺) V) (lift (𝓤 ⁺) x) ＝ η (Lift (𝓤 ⁺) V) (lift (𝓤 ⁺) y)
  → ¬¬ (x ＝ y)
 lemma-A-for-carriers-in-𝓤₀ = Euclidean.lemma-A ν κ

 lemma-B-for-carriers-in-𝓤
  : {M : 𝓤 ̇ } (S : M → 𝓤 ⁺ ̇ )
  → ((x : M) → is-prop (S x))
  → ((x y : M) → S x → ¬¬ (x ＝ y) → S y)
  → is-étale (λ (s : Σ z ꞉ Lift (𝓤 ⁺) M , S (lower z)) → pr₁ s)
 lemma-B-for-carriers-in-𝓤 =
  manifolds.lemma-B.inclusions-of-stable-subtypes-are-étale ν κ

 lemma-B-for-carriers-in-𝓤₀
  : {V : 𝓤₀ ̇ } (S : V → 𝓤 ⁺ ̇ )
  → ((x : V) → is-prop (S x))
  → ((x y : V) → S x → ¬¬ (x ＝ y) → S y)
  → is-étale (λ (s : Σ z ꞉ Lift (𝓤 ⁺) V , S (lower z)) → pr₁ s)
 lemma-B-for-carriers-in-𝓤₀ =
  Euclidean.lemma-B.inclusions-of-stable-subtypes-are-étale ν κ

\end{code}
