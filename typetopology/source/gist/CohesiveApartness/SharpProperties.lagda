Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: step K1 of Claude Fable 5.2's plan [1], as
released by GPT-6 Astra [2]. See the AI disclosure in
gist.CohesiveApartness.index.

Two properties of the native ♯, from function extensionality alone.

 * identifications-in-♯-from-sharp-ones: identifications in ♯ A can be
   obtained from sharp ones. This is the codiscreteness of the
   identity types of ♯ A [3, Theorem 3.7]. The two constant maps
   ♯ (u ＝ v) → ♯ A with values u and v agree on the image of the unit,
   and rec-sharp, which extends a map (u ＝ v) → ♯ A along the unit,
   sends the two restrictions to the two constant maps, by the η rule
   for ♯.

 * ♯-of-a-proposition-is-a-proposition: ♯ preserves propositions.

No axiom of cohesion is used, and function extensionality is an
ordinary hypothesis. The two lemmas used to be proved three times, by
the same code: in gist.RealCohesion.BoundaryRetractionFromC1Targets
(lines 92–103 of the frozen delivery r3), in gist.Orbifolds.CrispTruncation
(lines 63–74 there, from Claude Fable 5.2's scratch check
CrispTruncationCheck.lagda of 13 November 2026), and, the first one,
in gist.RealCohesion.BoundaryRetractionFromC1 (lines 180–183 there).
The code below is that code, unchanged except that function
extensionality is a parameter of this module; the three modules now
name these lemmas by typed aliases. Crisp elimination of propositional
truncations, which uses the second lemma, is in
gist.CohesiveApartness.CrispTruncation, so that a module that needs
only these lemmas does not depend on propositional truncations.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K1.
    references/F02-consolidation-plan.md

[2] GPT-6 Astra. Consolidation implementation, first release,
    13 November 2026.
    references/A26-consolidation-release-01.txt

[3] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Subsingletons

module gist.CohesiveApartness.SharpProperties
        (fe : Fun-Ext)
       where

open import UF.Base
open import gist.CohesiveApartness.Sharp

identifications-in-♯-from-sharp-ones
 : {𝓤 : Universe} {A : 𝓤 ̇ } (u v : ♯ A) → ♯ (u ＝ v) → u ＝ v
identifications-in-♯-from-sharp-ones {𝓤} {A} u v =
 happly (ap rec-sharp (dfunext fe (λ (p : u ＝ v) → p)))

♯-of-a-proposition-is-a-proposition
 : {𝓤 : Universe} {G : 𝓤 ̇ } → is-prop G → is-prop (♯ G)
♯-of-a-proposition-is-a-proposition i u v =
 identifications-in-♯-from-sharp-ones u v w
 where
  w : ♯ (u ＝ v)
  w .ε♯ = ap unit-sharp (i (u .ε♯) (v .ε♯))

\end{code}
