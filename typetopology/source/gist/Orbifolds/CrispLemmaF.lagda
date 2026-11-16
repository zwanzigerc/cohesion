Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H5 of Fable's roadmap [1].

Lemma F and Corollary F′ for crisp maps
---------------------------------------

The printed forms [1, Section 3.3]: for a modality ○ that preserves
crisp pullbacks,

  Lemma F. Let f : A → B be a crisp map of crisp types, K = A ×_B A,
  and p₂ : K → A. If f is surjective and p₂ is étale, then f is étale.

  Corollary F′. Let e : F → O be a crisp surjection of crisp sets with
  F modal. Then O is modal.

They are instances of lemma-F and corollary-F′ of LemmaF, which need
only that ○ preserves the kernel pair of the given map. Here the
hypothesis is the roadmap's: ○ preserves all crisp pullbacks
(○-preserves-crisp-pullbacks), the second half of core item 4 for ℑ.
Crisp means @♭ in Agda's --cohesion; the universe of the modality is
crisp, so that its types can be crisp variables. Corollary F′ also
needs that propositions are modal; for a nullification at pointed
types this is propositions-are-modal (Nullification), which gives
corollary-F′-for-nullifications. Of the two types only O needs to be a
set.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.3 and 4.
    references/F01-orbifolds-roadmap-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.CrispLemmaF
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        {@♭ 𝓤 : Universe}
        {𝓥 : Universe}
        (P : subuniverse 𝓤 𝓥)
        (P-is-reflective : subuniverse-is-reflective P)
        (P-is-sigma-closed : subuniverse-is-sigma-closed P)
        (P-is-replete : subuniverse-is-replete P)
       where

open import Modal.ReflectiveSubuniverse P P-is-reflective using (is-modal)
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.Pullback
open import UF.Sets
open import UF.Subsingletons

open import gist.Orbifolds.Modalities
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
 using (is-étale)
open import gist.Orbifolds.LemmaF
             fe pt P P-is-reflective P-is-sigma-closed P-is-replete
open import gist.Orbifolds.Nullification fe
 using (is-nullification ; propositions-are-modal)

○-preserves-crisp-pullbacks : 𝓤 ⁺ ̇
○-preserves-crisp-pullbacks =
 {@♭ A B C : 𝓤 ̇ } (@♭ f : A → C) (@♭ g : B → C) → ○-preserves-pullback f g

lemma-F-crisp : ○-preserves-crisp-pullbacks
              → {@♭ A B : 𝓤 ̇ } (@♭ f : A → B)
              → is-surjection f
              → is-étale (pullback.pb₂ f f)
              → is-étale f
lemma-F-crisp π f = lemma-F f (π f f)

corollary-F′-crisp : ○-preserves-crisp-pullbacks
                   → ((X : 𝓤 ̇ ) → is-prop X → is-modal X)
                   → {@♭ F O : 𝓤 ̇ } (@♭ e : F → O)
                   → is-surjection e
                   → is-set O
                   → is-modal F
                   → is-modal O
corollary-F′-crisp π props-are-modal e = corollary-F′ props-are-modal e (π e e)

module _ {𝓦 : Universe} {I : 𝓦 ̇ }
         (B : I → 𝓤 ̇ ) (b : (i : I) → B i)
         (ν : is-nullification B b P)
       where

 corollary-F′-for-nullifications : ○-preserves-crisp-pullbacks
                                 → {@♭ F O : 𝓤 ̇ } (@♭ e : F → O)
                                 → is-surjection e
                                 → is-set O
                                 → is-modal F
                                 → is-modal O
 corollary-F′-for-nullifications π =
  corollary-F′-crisp π (propositions-are-modal B b P ν)

\end{code}
