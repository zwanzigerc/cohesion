Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

A crisp quotient of a ♭-discrete type is ♭-discrete (gate G25): the
general form of Shulman's Lemma 8.24 [1] for the large quotients of
TypeTopology's Quotient.Large, which the second addendum asks for
before G25 ("to check in the library before starting", item (b)).

The proof is that of the quotient of levels in
gist.RealCohesion.FiniteChainDiscreteness, made generic. The counit
♭ (X/≈) → X/≈ is an embedding, because X/≈ is a crisp set and crisp
propositions are ♭-discrete (counit-on-crisp-sets of
gist.RealCohesion.CrispRationals); and it is a surjection, because every
element of X/≈ is merely the class of some x, which is the counit of a
crisp element of X since X is ♭-discrete, and the class of a crisp
element is crisp. The ♭-discreteness of crisp propositions is an
ordinary hypothesis, which Axiom R♭ gives; the one ingredient that
needs crisp identity induction, crisp-ap-^♭, is a module parameter, as
in gist.RealCohesion.FiniteChainDiscreteness.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispQuotients
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import UF.Equiv
open import UF.ImageAndSurjection pt
open import Quotient.Type using (EqRel)
open import Quotient.Large pt fe pe using (module large-quotient)
open import gist.RealCohesion.CrispRationals using (module counit-on-crisp-sets)

open PropositionalTruncation pt

module _ (crisp-props-are-♭-discrete : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ )
                                     → @♭ is-prop P → is-♭-discrete P)
       where

 open counit-on-crisp-sets crisp-ap-^♭ crisp-props-are-♭-discrete

 crisp-quotients-are-♭-discrete
  : {@♭ 𝓤 𝓥 : Universe} (@♭ X : 𝓤 ̇ ) (@♭ ≋ : EqRel {𝓤} {𝓥} X)
  → is-♭-discrete X
  → is-♭-discrete (large-quotient.X/≈ X ≋)
 crisp-quotients-are-♭-discrete {𝓤} {𝓥} X ≋ d =
  surjective-embeddings-are-equivs ♭-counit
   (♭-counit-is-embedding-on-crisp-sets (large-quotient.X/≈ X ≋)
     (large-quotient.X/≈-is-set X ≋))
   surjection
  where
   s : X → ♭ X
   s = pr₁ (pr₁ d)

   ε : ♭-counit ∘ s ∼ id
   ε = pr₂ (pr₁ d)

   surjection : is-surjection (♭-counit {𝓤 ⊔ 𝓥 ⁺} {large-quotient.X/≈ X ≋})
   surjection = large-quotient.quotient-induction X ≋
                 (λ c → ∃ u ꞉ ♭ (large-quotient.X/≈ X ≋) , ♭-counit u ＝ c)
                 (λ c → ∃-is-prop) I
    where
     I : (x : X)
       → ∃ u ꞉ ♭ (large-quotient.X/≈ X ≋) , ♭-counit u ＝ large-quotient.η X ≋ x
     I x = ∣ γ (s x) (ε x) ∣
      where
       γ : (u : ♭ X) → ♭-counit u ＝ x
         →
         Σ w ꞉ ♭ (large-quotient.X/≈ X ≋) , ♭-counit w ＝ large-quotient.η X ≋ x
       γ (v ^♭) e = large-quotient.η X ≋ v ^♭ , ap (large-quotient.η X ≋) e

\end{code}
