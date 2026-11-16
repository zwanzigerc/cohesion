Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; prose corrected 13 November 2026, after
the final audits. See the AI disclosure in gist.RealCohesion.index.

The approximate intermediate value theorem for arbitrary functions,
from Axiom R♭ alone.

This answers nLab problem 4 in its strict reading: crispness can be
removed from Shulman's approximate intermediate value theorem
[2, Theorem 11.4] assuming only Axiom R♭. The mathematics is Theorem E
of the proof note [1], by Claude Fable 5.2, audited by GPT-6 Astra, in
the form of revision 3 of the formalization blueprint [3]: the
finite-chain lemma, Astra's sequential hitting, and soft bisection
with a two-case conclusion.

For f : ℝ → ℝ and p q a b : ℝ, none of them crisp, with p < q,
f a < q and p < f b, there merely is x with p < f x < q. This is
crisp-approximate-IVT of gist.RealCohesion.CrispDiscreteness with
every crispness annotation removed, and it is the type Approximate-IVT
of the starter module of [3].

The proof combines two independent parts.

 * The modal part (gist.RealCohesion.FiniteChainDiscreteness): under
   Axiom R♭, the quotient Q of levels by finite chains is ♭-discrete,
   so every map ℝ → Q is constant. This uses the ♭-discreteness of 𝟚
   and the module parameter crisp-ap-^♭, both proved in --safe mode
   from the native ♯ in gist.CohesiveApartness.CrispInduction, which
   gist.RealCohesion.Theorems uses, and with --flat-split in the
   FlatSplit modules, which are not --safe.

 * The analytic part, which assumes only that every map ℝ → Q is
   constant and is otherwise --safe --without-K without --cohesion:
   the finite-chain lemma (gist.RealCohesion.FiniteChainLemma),
   sequential hitting (gist.RealCohesion.SequentialHitting), soft
   bisection and the normal form (gist.RealCohesion.SoftBisection),
   and the reduction to the normal form
   (gist.RealCohesion.ApproximateIVTReduction), over the real-number
   layer of gist.RealCohesion.RealLattice and
   gist.RealCohesion.RealLimits.

No excluded middle, Markov principle, Axiom T, choice, univalence or
set-quotient axiom is assumed. The assumptions are those of the module
parameters and theorem hypotheses below: function extensionality,
propositional extensionality, propositional truncations, crisp-ap-^♭,
Axiom R♭ and the ♭-discreteness of 𝟚. The last two are ordinary, not
crisp, hypotheses, which makes the theorem stronger.

We also export the normal form and sequential hitting under Axiom R♭.
All three results have the types that the starter module
gist.RealCohesion.ApproximateIVTStatement fixed before the
formalization started.

[1] The approximate intermediate value theorem from real cohesion
    alone. Proof note by Claude Fable 5.2, revision 2, 10 November
    2026, audited by GPT-6 Astra.
    references/F17-aivt-proof-rev2.md

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[3] Formalization blueprint: the approximate IVT from Axiom R♭.
    Claude Fable 5.2, revision 3, 10 November 2026.
    references/F15-aivt-blueprint-rev3.md
    references/F16-aivt-handoff-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.ApproximateIVT
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import Rationals.Type
open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
open import gist.RealCohesion.ApproximateIVTStatement fe pe pt
 using (Approximate-IVT ; Normal-Form ; Sequential-Hitting)
open import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭
 using (maps-from-ℝ-to-Q-are-constant)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (sequential-hitting-as-stated)
open import gist.RealCohesion.SoftBisection fe pe pt using (normal-form)
open import gist.RealCohesion.ApproximateIVTReduction fe pe pt
 using (approximate-IVT-from-constancy)

\end{code}

The theorem, the normal form and sequential hitting under Axiom R♭,
with the types of the starter module
gist.RealCohesion.ApproximateIVTStatement.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 approximate-IVT : Approximate-IVT
 approximate-IVT = approximate-IVT-from-constancy
                    (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 approximate-IVT-normal-form : Normal-Form 1/3 2/3
 approximate-IVT-normal-form =
  normal-form (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 sequential-hitting : Sequential-Hitting
 sequential-hitting =
  sequential-hitting-as-stated
   (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

\end{code}
