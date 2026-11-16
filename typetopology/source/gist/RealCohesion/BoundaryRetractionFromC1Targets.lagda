Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026, for gate G27 of the second addendum to the
formalization plan, answering a point of GPT-6 Astra's review of that
gate. Added to the folder by Claude Opus 5.5 on 12 November 2026, after
Astra's review released it, with one change that Astra asked for: the
equality bits-agree, which the module took from
gist.RealCohesion.Theorems, is repeated here (§3), so that Theorems can
import this module without a cycle. On 13 November 2026, in the
consolidation after the final audits, Claude Opus 5.5 made the two
lemmas of §1 typed aliases of those of
gist.CohesiveApartness.SharpProperties, and, since both statements of
Kuhn's lemma now come from gist.RealCohesion.KuhnStatement, made
bits-agree refl and removed the transport along it (§3). See the AI
disclosure in gist.RealCohesion.index.

The modules gist.RealCohesion.BoundaryRetractionFromC1 and
gist.RealCohesion.BoundaryRetractionFromC1Statements take Axiom C1,
and Axiom R♭ in the specialization, as crisp hypotheses. The targets
Target-3-7-crisp and Target-3-7-sharp of
gist.RealCohesion.BrouwerStatements take Axiom R♭ as an ordinary
hypothesis. So the specialization does not have the type of the
targets. This module gives the bridge.

 * Under Axiom R♭, or Axiom C1, as an ordinary hypothesis, every crisp
   proposition G is codiscrete: ♯ G → G. This generalizes
   [1, Theorem 8.11], which is the case of the empty type. The
   proposition ♯ G is crisp, hence ♭-discrete [1, Lemma 8.8], so that
   an element of it comes from a crisp one, from which the element of
   G can be extracted.

 * Hence a crisp proposition that follows from a crisp proof of the
   axiom follows from an ordinary proof of it: the introduction rule
   of ♯ makes the proof crisp.

 * The fixed-point theorem for the cube from crisp excluded middle,
   Axiom C1 and "ℝ is not ♭-discrete", specialized to Axiom R♭, gives
   Target-3-7-crisp and Target-3-7-sharp with their own types. The
   existing proofs of these targets in gist.RealCohesion.Theorems are
   not used, and the targets are not changed.

 * The same theorem holds with Axiom C1 as an ordinary hypothesis, in
   its crisp and in its sharp form.

This does not apply to conclusions that are not crisp propositions:
the retraction of [1, Lemma 12.3], which is a structure and is given
for a map that is not crisp, is obtained from a crisp proof of Axiom
C1 only.

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

module gist.RealCohesion.BoundaryRetractionFromC1Targets
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import UF.Base
open import UF.Equiv
open import DedekindReals.Type fe pe pt
open import gist.CohesiveApartness.Sharp
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using
  (Cube ; bit ; Kuhn-Lemma ; Crisp-Cube-Fixed-Point ; Sharp-Cube-Fixed-Point ;
   crisp-fixed-points-give-sharp-fixed-points ;
   Target-3-7-crisp ; Target-3-7-sharp)
open import gist.RealCohesion.NativeSharp using (native-sharp)
import gist.RealCohesion.KuhnLemma as K
import gist.RealCohesion.BoundaryRetractionFromC1Statements
import gist.CohesiveApartness.SharpProperties

open PropositionalTruncation pt

private
 module S = gist.RealCohesion.BoundaryRetractionFromC1Statements fe pe pt
 module SP = gist.CohesiveApartness.SharpProperties fe

\end{code}

1. The modality ♯ preserves propositions. No axiom of cohesion is
used. The two lemmas are those of
gist.CohesiveApartness.SharpProperties, named here by typed aliases,
so that, as before, they take the parameters of this module.

\begin{code}

identifications-in-♯-from-sharp-ones
 : {𝓤 : Universe} {A : 𝓤 ̇ } (u v : ♯ A) → ♯ (u ＝ v) → u ＝ v
identifications-in-♯-from-sharp-ones = SP.identifications-in-♯-from-sharp-ones

♯-of-a-proposition-is-a-proposition
 : {𝓤 : Universe} {G : 𝓤 ̇ } → is-prop G → is-prop (♯ G)
♯-of-a-proposition-is-a-proposition = SP.♯-of-a-proposition-is-a-proposition

\end{code}

2. Crisp propositions are codiscrete, under Axiom R♭ as an ordinary
hypothesis.

\begin{code}

crisp-propositions-are-codiscrete
 : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
 → {@♭ 𝓣 : Universe} (@♭ G : 𝓣 ̇ ) → is-prop G → ♯ G → G
crisp-propositions-are-codiscrete r♭ G i z = γ (pr₁ (pr₁ d) z)
 where
  d : is-♭-discrete (♯ G)
  d = rl-implication (r♭ (♯ G))
       (λ h r → ♯-of-a-proposition-is-a-proposition i (h r) (h 0ℝ))

  γ : ♭ (♯ G) → G
  γ (w ^♭) = crisp-elim-sharp w

a-crisp-proof-of-R♭-suffices-for-crisp-propositions
 : {@♭ 𝓣 : Universe} (@♭ G : 𝓣 ̇ )
 → is-prop G
 → ((@♭ r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ) → G)
 → Singly-Generated-Punctual-Cohesion ℝ 0ℝ → G
a-crisp-proof-of-R♭-suffices-for-crisp-propositions G i φ r♭ =
 crisp-propositions-are-codiscrete r♭ G i w
 where
  w : ♯ G
  w .ε♯ = φ r♭

\end{code}

3. The targets. Their hypothesis Kuhn-Lemma n is passed unchanged to
gist.RealCohesion.BoundaryRetractionFromC1Statements, whose statement
of Kuhn's lemma, that of gist.RealCohesion.KuhnLemma, is the same:
bits-agree holds by refl, as in gist.RealCohesion.Theorems.

\begin{code}

bits-agree : K.bit ＝ bit
bits-agree = refl

C1-theorem-gives-Target-3-7-crisp : (@♭ n : ℕ) → Target-3-7-crisp n
C1-theorem-gives-Target-3-7-crisp n cem r♭ kuhn f =
 crisp-propositions-are-codiscrete r♭ (∃ x ꞉ Cube n , f x ＝ x) ∃-is-prop w
 where
  w : ♯ (∃ x ꞉ Cube n , f x ＝ x)
  w .ε♯ = S.crisp-fixed-points-from-LEM-and-R♭ r♭ cem {n} kuhn f

C1-theorem-gives-Target-3-7-sharp : (@♭ n : ℕ) → Target-3-7-sharp native-sharp n
C1-theorem-gives-Target-3-7-sharp n cem r♭ kuhn =
 crisp-fixed-points-give-sharp-fixed-points native-sharp n
  (C1-theorem-gives-Target-3-7-crisp n cem r♭ kuhn)

\end{code}

4. The same for Axiom C1 as an ordinary hypothesis.

\begin{code}

module _ {@♭ 𝓥 𝓦 : Universe} {@♭ J : 𝓥 ̇ }
         (@♭ R : J → 𝓦 ̇ )
       where

 crisp-propositions-are-codiscrete-under-C1
  : Axiom-C1 R
  → {@♭ 𝓣 : Universe} (@♭ G : 𝓣 ̇ ) → is-prop G → ♯ G → G
 crisp-propositions-are-codiscrete-under-C1 c1 G i z = γ (pr₁ (pr₁ d) z)
  where
   open Axiom-C1 c1

   d : is-♭-discrete (♯ G)
   d = rl-implication (axiom-C0 (♯ G))
        (λ j → rl-implication
                (null-iff-maps-are-constant fe (R j) (base-point j) (♯ G))
                (λ h r → ♯-of-a-proposition-is-a-proposition i (h r)
                          (h (base-point j))))

   γ : ♭ (♯ G) → G
   γ (w ^♭) = crisp-elim-sharp w

 a-crisp-proof-of-C1-suffices-for-crisp-propositions
  : {@♭ 𝓣 : Universe} (@♭ G : 𝓣 ̇ )
  → is-prop G
  → ((@♭ c1 : Axiom-C1 R) → G)
  → Axiom-C1 R → G
 a-crisp-proof-of-C1-suffices-for-crisp-propositions G i φ c1 =
  crisp-propositions-are-codiscrete-under-C1 c1 G i w
  where
   w : ♯ G
   w .ε♯ = φ c1

 crisp-fixed-points-from-LEM-ordinary-C1-and-ℝ-not-♭-discrete
  : Axiom-C1 R
  → (@♭ cem₀ : Crisp-EM 𝓤₀)
  → ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
  → (@♭ f : Cube n → Cube n) → ∃ x ꞉ Cube n , f x ＝ x
 crisp-fixed-points-from-LEM-ordinary-C1-and-ℝ-not-♭-discrete c1 cem₀ nd {n}
  kuhn f =
  crisp-propositions-are-codiscrete-under-C1 c1 (∃ x ꞉ Cube n , f x ＝ x)
   ∃-is-prop w
  where
   w : ♯ (∃ x ꞉ Cube n , f x ＝ x)
   w .ε♯ =
    S.crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete R c1 cem₀ nd kuhn f

 sharp-fixed-points-from-LEM-ordinary-C1-and-ℝ-not-♭-discrete
  : Axiom-C1 R
  → (@♭ cem₀ : Crisp-EM 𝓤₀)
  → ¬ is-♭-discrete ℝ
  → {@♭ n : ℕ} (@♭ kuhn : K.Kuhn-Lemma n)
  → (f : Cube n → Cube n) → ♯ (∃ x ꞉ Cube n , f x ＝ x)
 sharp-fixed-points-from-LEM-ordinary-C1-and-ℝ-not-♭-discrete c1 cem₀ nd {n}
  kuhn f = w
  where
   w : ♯ (∃ x ꞉ Cube n , f x ＝ x)
   w .ε♯ =
    S.crisp-fixed-points-from-LEM-C1-and-ℝ-not-♭-discrete R c1 cem₀ nd kuhn f

\end{code}
