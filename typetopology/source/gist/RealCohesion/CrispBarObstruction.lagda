Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index. Following a gameplan by Codex (25 October
2026) [1].

The obstructions of gist.RealCohesion.AnalyticMarkovObstruction with
crisp data.

In the pointless-end countermodel the data X, t and B of the
obstructions are crisp: they are given externally, by a locale, its
coordinate and a family of its opens. The conditions on them, and the
principles that they refute, still quantify over arbitrary elements of
X. This module records that the theorems apply to crisp data, and
explains why the quantifiers must stay ordinary: under crisp excluded
middle, a dense positive family is positive at every crisp element.
So restricting the properness condition to crisp elements would make
it contradict crisp excluded middle, rather than refute the analytic
Markov principle.

This is consistent with the analytic Markov principle for crisp real
numbers, which follows from crisp excluded middle
(gist.RealCohesion.CrispDiscreteness). The obstructions concern
arbitrary real numbers.

[1] Codex. Gameplan for Opus: syntactic refutations of analytic Markov
    and full FAN, 25 October 2026.
    references/C09b-agda-conditional-refutations.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispBarObstruction
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import MLTT.List hiding ([_])
open import Notation.Order
open import UF.SubtypeClassifier
open import gist.RealCohesion.AnalyticMarkovObstruction fe pe pt
open import gist.RealCohesion.BinaryBarObstruction pt fe

\end{code}

Crisp data, ordinary conclusions. The data and the proof of the
conditions are crisp variables, used in ordinary positions.

\begin{code}

module _ {@♭ 𝓤 𝓥 : Universe}
         (@♭ X : 𝓤 ̇ )
         (@♭ t : X → ℝ)
         (@♭ B : X → List 𝟚 → Ω 𝓥)
         (@♭ 𝓑 : Five-Conditions X t B)
       where

 crisp-five-conditions-refute-both : ¬ Analytic-Markov × ¬ Full-FAN 𝓥
 crisp-five-conditions-refute-both = five-conditions-refute-both 𝓑

module _ {@♭ 𝓤 : Universe}
         (@♭ X : 𝓤 ̇ )
         (@♭ t : X → ℝ)
         (@♭ dense-positive : (x : X) → ¬¬ (0ℝ < t x))
         (@♭ proper-positive : ¬ ((x : X) → 0ℝ < t x))
       where

 crisp-dense-positive-family-refutes-analytic-Markov : ¬ Analytic-Markov
 crisp-dense-positive-family-refutes-analytic-Markov =
  dense-positive-family-refutes-analytic-Markov
   X t dense-positive proper-positive

\end{code}

Under crisp excluded middle, a crisp dense positive family is positive
at crisp elements, and so properness for crisp elements fails. The
density proof needn't be crisp.

\begin{code}

module _ {@♭ 𝓤 : Universe}
         {@♭ X : 𝓤 ̇ }
         (@♭ t : X → ℝ)
         (dense-positive : (x : X) → ¬¬ (0ℝ < t x))
       where

 dense-positive-family-is-positive-at-crisp-elements
  : Crisp-EM 𝓤₀ → (@♭ x : X) → 0ℝ < t x
 dense-positive-family-is-positive-at-crisp-elements cem x =
  cases id (λ ν → 𝟘-elim (dense-positive x ν))
   (cem (0ℝ < t x) (<-is-prop 0ℝ (t x)))

 crisp-properness-contradicts-crisp-EM
  : Crisp-EM 𝓤₀ → ¬ ¬ ((@♭ x : X) → 0ℝ < t x)
 crisp-properness-contradicts-crisp-EM cem crisp-proper =
  crisp-proper (dense-positive-family-is-positive-at-crisp-elements cem)

\end{code}
