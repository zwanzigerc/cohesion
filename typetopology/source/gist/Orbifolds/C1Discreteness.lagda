Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time); the proofs shared with
gist.RealCohesion.PunctualCohesion later that day, in the consolidation
after the final audits [4]. Orbifold gate H10 of Fable's roadmap [1],
for the target T5b.

Two consequences of Axiom C1
----------------------------

Axiom C1 of the module gist.CohesiveApartness.Flat, for an arbitrary
family of pointed generators: a crisp type is ♭-discrete exactly when it
is null for every generator, and every generator has a point.

  crisp-propositions-are-♭-discrete : maps from a pointed type into a
  proposition are constant;

  crisp-witnesses : so an ordinary proof of a crisp proposition gives a
  crisp one, under ♭ (the inverse of the counit);

  types-with-decidable-equality-are-♭-discrete : the valid direction of
  Shulman's Lemma 8.15, from C1 alone [2, Section 2; 3, Section B]: for
  a map f from a generator into a crisp type X with decidable equality,
  the test y ↦ [f y = f (base point)], with values in 𝟚, is constant
  because 𝟚 is ♭-discrete (CrispInduction), hence null, so f is
  constant; so X is null for every generator and ♭-discrete by C0. The
  decidable equality may be an ordinary proof.

Since the consolidation, the first and the third are typed aliases of
the statements of gist.RealCohesion.PunctualCohesion, for the ordinary
family and C1 of this module, and the test of the third takes values
in 𝟚 (gist.RealCohesion.BooleanTests) where it used to take values 0
and 1 in ℕ. The names, the types and the module parameters, a crisp
function extensionality and an ordinary C1, are unchanged.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. DP properness implies the replacement over the
    five-item core, 11 November 2026.
    references/A02-dp-properness-implies-replacement.txt
[3] GPT-6 Astra. H10 T5b implementation preflight, 13 November 2026
    (UTC).
    references/A24-t5b-preflight.txt
[4] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K4, as corrected by its
    addendum 01 (whose scratch check C1DiscretenessWrapperCheck.lagda,
    SHA-256 938af4ca…, these aliases follow) and released by GPT-6
    Astra.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt

module gist.Orbifolds.C1Discreteness (@♭ fe : Fun-Ext) where

open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.Equiv
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat
 using (♭ ; _^♭ ; ♭-counit ; is-♭-discrete ; Axiom-C1)
open import gist.CohesiveApartness.CrispInduction using (𝟚-is-♭-discrete)
import gist.RealCohesion.PunctualCohesion

private
 module PC = gist.RealCohesion.PunctualCohesion fe

module _ {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ } (c1 : Axiom-C1 Gen) where

 crisp-propositions-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → is-prop P → is-♭-discrete P
 crisp-propositions-are-♭-discrete = PC.crisp-propositions-are-♭-discrete Gen c1

 crisp-witnesses : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → is-prop P → P → ♭ P
 crisp-witnesses P i = inverse ♭-counit (crisp-propositions-are-♭-discrete P i)

 types-with-decidable-equality-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ X : 𝓣 ̇ ) → is-discrete X → is-♭-discrete X
 types-with-decidable-equality-are-♭-discrete =
  PC.types-with-decidable-equality-are-♭-discrete Gen c1 𝟚-is-♭-discrete

\end{code}
