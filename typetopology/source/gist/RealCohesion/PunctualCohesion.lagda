Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: step K4 of Claude Fable 5.2's plan [1], as
corrected by its addendum [2] and released by GPT-6 Astra [3]. See the
AI disclosure in gist.RealCohesion.index.

Consequences of Axiom C1 for an ordinary family of generators
-------------------------------------------------------------

For a family R : J → 𝓦 of pointed generators with Axiom C1
[4, §8.2], both ordinary hypotheses, and crisp types:

 1. generator-maps-are-constant: a ♭-discrete type A is null for every
    generator, so maps R j → A are constant;

 2. types-null-for-the-generators-are-♭-discrete: the converse;

 3. crisp-propositions-are-♭-discrete [4, Lemma 8.8], with an ordinary
    proof of propositionality;

 4. maps-into-♭-discrete-types-are-♭-discrete: D → A is ♭-discrete if
    A is, for crisp D and A in independent universes;

 5. types-with-decidable-equality-are-♭-discrete, from the
    ♭-discreteness of 𝟚, an explicit premise of this statement only,
    by gist.RealCohesion.BooleanTests.

The only module parameter is function extensionality: no Q, no real
numbers, no propositional extensionality, no truncations, no crisp-ap,
no native ♯. The family and Axiom C1 are ordinary, so that the
statements apply to an ordinary proof of Axiom C1, and in particular
to Axiom R♭ as an ordinary hypothesis (it gives Axiom C1 for the one
generator ℝ by singly-generated-punctual-cohesion-gives-Axiom-C1 of
gist.CohesiveApartness.Flat). The crispness that C0 needs comes from
the types to which it is applied, never from c1. A module with a crisp
family or a crisp c1 passes them here as ordinary arguments.

These statements used to be proved separately: from Axiom C1 in
gist.RealCohesion.CrispDiscreteness, gist.RealCohesion.BoundaryRetractionFromC1
and gist.Orbifolds.C1Discreteness, and from Axiom R♭ in
gist.RealCohesion.FiniteChainDiscreteness,
gist.RealCohesion.DiscreteSets, gist.RealCohesion.RealSubsetShape and
gist.RealCohesion.ApproximateBrouwerSquare. Those modules keep their
names and types, as typed aliases or instances of these.

Source. The code is Claude Fable 5.2's scratch check
PunctualCohesionCheck.lagda (SHA-256 cab9c538…, in the companion of
[2]), adapted only in the module name, the import of
gist.RealCohesion.BooleanTests and the header. Its proofs are those of
the copies named above, written once for a general family.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K4.
    references/F02-consolidation-plan.md

[2] Claude Fable 5.2. Addendum 01 to the consolidation plan,
    13 November 2026, Section 1.
    references/F03-consolidation-plan-addendum-01.md

[3] GPT-6 Astra. Consolidation implementation, second release,
    13 November 2026.
    references/A27-consolidation-release-02.txt

[4] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt

module gist.RealCohesion.PunctualCohesion (fe : Fun-Ext) where

open import UF.Base
open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.Equiv
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.BooleanTests

module _ {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R) where

 open Axiom-C1 c1

 generator-maps-are-constant
  : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ ) → is-♭-discrete A
  → (j : J) (f : R j → A) (r : R j) → f r ＝ f (base-point j)
 generator-maps-are-constant A d j =
  lr-implication (null-iff-maps-are-constant fe (R j) (base-point j) A)
   (lr-implication (axiom-C0 A) d j)

 types-null-for-the-generators-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ A : 𝓣 ̇ )
  → ((j : J) (f : R j → A) (r : R j) → f r ＝ f (base-point j))
  → is-♭-discrete A
 types-null-for-the-generators-are-♭-discrete A κ =
  rl-implication (axiom-C0 A)
   (λ j → rl-implication
           (null-iff-maps-are-constant fe (R j) (base-point j) A) (κ j))

 crisp-propositions-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → is-prop P → is-♭-discrete P
 crisp-propositions-are-♭-discrete P i =
  types-null-for-the-generators-are-♭-discrete P
   (λ j f r → i (f r) (f (base-point j)))

 maps-into-♭-discrete-types-are-♭-discrete
  : {@♭ 𝓣 𝓣' : Universe} (@♭ D : 𝓣 ̇ ) (@♭ A : 𝓣' ̇ )
  → is-♭-discrete A → is-♭-discrete (D → A)
 maps-into-♭-discrete-types-are-♭-discrete D A d =
  types-null-for-the-generators-are-♭-discrete (D → A)
   (λ j f r → dfunext fe
               (λ x → generator-maps-are-constant A d j (λ s → f s x) r))

 types-with-decidable-equality-are-♭-discrete
  : is-♭-discrete 𝟚
  → {@♭ 𝓣 : Universe} (@♭ X : 𝓣 ̇ ) → is-discrete X → is-♭-discrete X
 types-with-decidable-equality-are-♭-discrete 𝟚-is-♭-discrete X δ =
  types-null-for-the-generators-are-♭-discrete X
   (λ j → maps-into-types-with-decidable-equality-are-constant
           (R j) (base-point j)
           (generator-maps-are-constant 𝟚 𝟚-is-♭-discrete j) X δ)

\end{code}
