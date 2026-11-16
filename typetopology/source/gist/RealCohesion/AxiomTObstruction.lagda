Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index. Following the plan [2], whose Agda part was
prepared by Codex (25 October 2026).

Conditional refutation of Shulman's Axiom T.

Shulman's Axiom T says that, for every real number x, the proposition
x > 0 is codiscrete [1, §8.3]. Shulman derives the analytic Markov
principle from Axioms LEM, C1 and T [1, Theorem 8.32], through his
Corollary 8.12, which says that ♯ P ≃ ¬¬ P for every proposition P,
assuming Axioms LEM and C1. The order form of the analytic Markov
principle needs less: that a codiscrete proposition is stable under
double negation. This is one direction of [1, Theorem 3.15(1)], and
Shulman notes in its proof that it uses crisp excluded middle but not
Axiom ♯∅, which is what Axiom C1 supplies [1, Theorem 8.11]. So the
obstructions of gist.RealCohesion.AnalyticMarkovObstruction refute
Axiom T in the presence of crisp excluded middle, without Axiom C1.
The apartness form of the principle, which is the form of Shulman's
Theorem 8.32, follows from the order form by
gist.RealCohesion.AnalyticMarkovObstruction, also without Axiom C1
(Axiom-T-gives-analytic-Markov-for-apartness).

We prove the direction that we need directly. To show ♯ P from ¬¬ P,
crisp induction for ♯ lets us assume that P and the proof of ¬¬ P are
crisp, and then crisp excluded middle decides P.

The modality ♯ is not available in Agda 2.8, so this module takes it
as the record of assumptions gist.RealCohesion.Sharp.Sharp-Modality,
of which only the unit and crisp induction are used here. This is an
assumed interface, not a model of ♯. A codiscrete type is one whose
unit has a retraction. Shulman asks for the unit to be an equivalence,
which is stronger, so assuming Axiom T with our notion of
codiscreteness assumes less, and its refutation is a stronger result.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

[2] The ordinary pointless-end countermodel: a formalization plan,
    revision 3, 25 October 2026. In particular its parts
    OBSTRUCTION-VERIFICATION.md and AGDA-CONDITIONAL-REFUTATIONS.md.
    references/C09-pointless-end-gameplan-v3.md
    references/C09a-obstruction-verification.md
    references/C09b-agda-conditional-refutations.md

[3] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.Sharp

module gist.RealCohesion.AxiomTObstruction
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (S : Sharp-Modality)
       where

open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import MLTT.List hiding ([_])
open import Notation.Order
open import UF.Retracts
open import UF.SubtypeClassifier
open import gist.RealCohesion.AnalyticMarkovObstruction fe pe pt
open import gist.RealCohesion.BinaryBarObstruction pt fe
open import gist.RealCohesion.PositiveTerms fe pe pt
 using (sum-is-positive-iff-some-term-is) renaming (sum to sum-of-terms)

open Sharp-Modality S
open PropositionalTruncation pt using (Exists ; ∃-is-prop)

\end{code}

Under crisp excluded middle, double negation gives ♯, and a codiscrete
proposition is stable under double negation. Crisp induction is used
over the type of propositions with a proof of their double negation.
We write this type out, rather than naming it, because it has to be
crisp: a definition in this module would depend on the module
parameters, which are not crisp.

\begin{code}

module _ {@♭ 𝓤 : Universe} (cem : Crisp-EM 𝓤) where

 private
  decide : (@♭ a : Σ p ꞉ Ω 𝓤 , ¬¬ (p holds)) → pr₁ a holds
  decide a = cases id (λ ν → 𝟘-elim (pr₂ a ν))
              (cem (pr₁ a holds) (holds-is-prop (pr₁ a)))

 ¬¬-gives-♯ : (p : Ω 𝓤) → ¬¬ (p holds) → ♯ (p holds)
 ¬¬-gives-♯ p h = crisp-ind-sharp {A = Σ p ꞉ Ω 𝓤 , ¬¬ (p holds)}
                   (λ a → pr₁ a holds) decide (p , h)

 codiscrete-props-are-¬¬-stable : (p : Ω 𝓤)
                                → is-codiscrete S (p holds)
                                → ¬¬ (p holds) → p holds
 codiscrete-props-are-¬¬-stable p κ h =
  retraction-of unit-sharp κ (¬¬-gives-♯ p h)

\end{code}

Axiom T, and the analytic Markov principle from it.

\begin{code}

Axiom-T : 𝓤₁ ̇
Axiom-T = (r : ℝ) → is-codiscrete S (0ℝ < r)

Axiom-T-gives-stability : Crisp-EM 𝓤₀ → Axiom-T → Positivity-Is-Stable
Axiom-T-gives-stability cem T r =
 codiscrete-props-are-¬¬-stable cem ((0ℝ < r) , <-is-prop 0ℝ r) (T r)

Axiom-T-gives-analytic-Markov : Crisp-EM 𝓤₀ → Axiom-T → Analytic-Markov
Axiom-T-gives-analytic-Markov cem T =
 stability-gives-analytic-Markov (Axiom-T-gives-stability cem T)

Axiom-T-gives-analytic-Markov-for-apartness : Crisp-EM 𝓤₀ → Axiom-T
                                            → Analytic-Markov-For-Apartness
Axiom-T-gives-analytic-Markov-for-apartness cem T =
 analytic-Markov-gives-apartness-version (Axiom-T-gives-analytic-Markov cem T)

\end{code}

Lemma 4.1 of the write-up [3]: under Axiom T, the proposition that some
term of a sequence of real numbers is positive is codiscrete. Axiom T
makes 0 < m codiscrete for the real number m of
gist.RealCohesion.PositiveTerms, which is positive exactly when some
term is, and codiscreteness of propositions passes along logical
equivalence. Neither excluded middle nor Axiom C1 is used.

\begin{code}

Axiom-T-gives-positive-terms-are-codiscrete
 : Axiom-T → (x : ℕ → ℝ) → is-codiscrete S (∃ k ꞉ ℕ , 0ℝ < x k)
Axiom-T-gives-positive-terms-are-codiscrete T x =
 codiscreteness-of-props-is-invariant-under-↔ S ∃-is-prop
  (sum-is-positive-iff-some-term-is x) (T (sum-of-terms x))

\end{code}

The conditional refutations. Neither needs Axiom C1, and neither uses
any property of ♯ beyond the interface.

\begin{code}

dense-positive-family-refutes-Axiom-T
 : Crisp-EM 𝓤₀
 → {𝓤 : Universe}
   (X : 𝓤 ̇ )
   (t : X → ℝ)
 → ((x : X) → ¬¬ (0ℝ < t x))
 → ¬ ((x : X) → 0ℝ < t x)
 → ¬ Axiom-T
dense-positive-family-refutes-Axiom-T cem X t dense proper T =
 dense-positive-family-refutes-stability X t dense proper
  (Axiom-T-gives-stability cem T)

five-conditions-refute-Axiom-T
 : Crisp-EM 𝓤₀
 → {𝓤 𝓥 : Universe}
   {X : 𝓤 ̇ }
   {t : X → ℝ}
   {B : X → List 𝟚 → Ω 𝓥}
 → Five-Conditions X t B
 → ¬ Axiom-T
five-conditions-refute-Axiom-T cem {𝓤} {𝓥} {X} {t} {B} 𝓑 =
 dense-positive-family-refutes-Axiom-T cem X t
  (five-conditions-give-dense-positive 𝓑)
  (Five-Conditions.proper 𝓑)

\end{code}
