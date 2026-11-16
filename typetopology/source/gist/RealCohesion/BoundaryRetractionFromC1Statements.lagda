Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Companion to
gist.RealCohesion.BoundaryRetractionFromC1, for gate G27 of the second
addendum to the formalization plan.

Added to the folder by Claude Opus 5.5 on 12 November 2026, for gate G27(b),
with the code and the prose unchanged, after GPT-6 Astra's review released it
(12 November 2026); see the AI disclosure in gist.RealCohesion.index.

The theorems of gist.RealCohesion.BoundaryRetractionFromC1 with their
types written out, so that the statements can be read without that
module's definitions, and the check that their hypotheses follow from
Axiom R♭.

 * Lemma-12-3-for-the-square-from-LEM-and-C1: [1, Lemma 12.3], with
   the square [-1,1]² in place of the disc, from crisp excluded middle
   and Axiom C1. Neither Axiom T nor Axiom R♭ is assumed, the map f is
   not assumed crisp, and the conclusion is a retraction.

 * discrete-or-no-fixed-point-free-maps-from-LEM-and-C1: under the
   same hypotheses, either ℝ is ♭-discrete or no self-map of the cube
   is fixed-point free.

 * crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete and
   sharp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete: the fixed-point
   theorems for the cube ([1, Corollary 12.5 and Theorem 12.4] for the
   square), from crisp excluded middle for 𝓤₀, Axiom C1, and the
   hypothesis that ℝ is not ♭-discrete.

 * Axiom R♭ gives Axiom C1, with ℝ as the only generator, and that ℝ
   is not ♭-discrete. So the last two theorems have the fixed-point
   theorems from crisp excluded middle and Axiom R♭ as instances. The
   converse fails in models: for the Dedekind real numbers of the
   smooth models, Axiom C1 holds and ℝ is not ♭-discrete, but Axiom R♭
   fails. That is not formalized.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.BoundaryRetractionFromC1Statements
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.Order
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Sharp
open import gist.RealCohesion.BrouwerStatements fe pe pt using (Cube)
open import gist.RealCohesion.KuhnLemma using (Kuhn-Lemma)
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using (is-retraction-onto-the-boundary)
import gist.RealCohesion.BoundaryRetractionFromC1

open PropositionalTruncation pt

\end{code}

The theorems, for a family R of generators with Axiom C1.

\begin{code}

module _ {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
         (@♭ R : J → 𝓦 ̇ )
         (@♭ c1 : Axiom-C1 R)
       where

 private
  module B = gist.RealCohesion.BoundaryRetractionFromC1 fe pe pt R c1

 Lemma-12-3-for-the-square-from-LEM-and-C1
  : (@♭ cem₀ : Crisp-EM 𝓤₀)
  → Crisp-EM 𝓤₁
  → (f : Cube 2 → Cube 2)
  → ((x : Cube 2) → ¬ (f x ＝ x))
  → Σ r ꞉ (Cube 2 → Cube 2) , is-retraction-onto-the-boundary r
 Lemma-12-3-for-the-square-from-LEM-and-C1 = B.Lemma-12-3-for-the-square

 Lemma-12-3-for-the-cube-from-LEM-and-C1
  : (@♭ cem₀ : Crisp-EM 𝓤₀)
  → Crisp-EM 𝓤₁
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma (succ n))
  →
  (Σ f ꞉ (Cube (succ n) → Cube (succ n)) , ((x : Cube (succ n)) → ¬ (f x ＝ x)))
  → Σ r ꞉ (Cube (succ n) → Cube (succ n)) , is-retraction-onto-the-boundary r
 Lemma-12-3-for-the-cube-from-LEM-and-C1 cem₀ cem₁ =
  B.Lemma-12-3-for-the-cube cem₀ cem₁

 discrete-or-no-fixed-point-free-maps-from-LEM-and-C1
  : (@♭ cem₀ : Crisp-EM 𝓤₀)
  → Crisp-EM 𝓤₁
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → is-♭-discrete ℝ
  ∔ ¬ (Σ f ꞉ (Cube n → Cube n) , ((x : Cube n) → ¬ (f x ＝ x)))
 discrete-or-no-fixed-point-free-maps-from-LEM-and-C1 cem₀ cem₁ =
  B.discrete-or-no-fixed-point-free-maps cem₀ cem₁

 crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete
  : (@♭ cem₀ : Crisp-EM 𝓤₀)
  → ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
 crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete cem₀ =
  B.crisp-fixed-points-if-ℝ-is-not-♭-discrete cem₀

 sharp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete
  : (@♭ cem₀ : Crisp-EM 𝓤₀)
  → ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)
 sharp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete cem₀ =
  B.sharp-fixed-points-if-ℝ-is-not-♭-discrete cem₀

 separators-make-ℝ-♭-discrete
  : (e : ℝ → 𝟚) (a b : ℝ) → e a ≠ e b → is-♭-discrete ℝ
 separators-make-ℝ-♭-discrete = B.separators-make-ℝ-discrete

 ♯𝟘-is-empty-from-C1 : ♯ (𝟘 {𝓤₀}) → 𝟘 {𝓤₀}
 ♯𝟘-is-empty-from-C1 = B.♯𝟘-is-empty

 ♭-detects-emptiness-from-C1
  : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ ) → ¬ ♭ A → ¬ A
 ♭-detects-emptiness-from-C1 = B.♭-detects-emptiness

\end{code}

Axiom R♭ gives the hypotheses: Axiom C1 for the single generator ℝ,
pointed by 0, and that ℝ is not ♭-discrete, because its identity map
is not constant. So the fixed-point theorem from crisp excluded middle
and Axiom R♭ is an instance.

\begin{code}

module _ (@♭ r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ) where

 R♭-gives-C1 : Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
 R♭-gives-C1 = singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭

 R♭-gives-that-ℝ-is-not-♭-discrete : ¬ is-♭-discrete ℝ
 R♭-gives-that-ℝ-is-not-♭-discrete d =
  <ℝ-irreflexive 0ℝ
   (transport (λ - → 0ℝ < -) (lr-implication (r♭ ℝ) d id 1ℝ)
     ℝ-zero-less-than-one)

 crisp-fixed-points-from-LEM-and-R♭
  : (@♭ cem₀ : Crisp-EM 𝓤₀)
  → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
  → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
 crisp-fixed-points-from-LEM-and-R♭ cem₀ =
  crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete
   (λ (_ : 𝟙 {𝓤₀}) → ℝ) R♭-gives-C1 cem₀ R♭-gives-that-ℝ-is-not-♭-discrete

\end{code}
