Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: step K2 of Claude Fable 5.2's plan [1], as
released by GPT-6 Astra [2]. See the AI disclosure in
gist.RealCohesion.index.

The statement of Kuhn's cubical lemma.

Kuhn-Lemma n is Kuhn's cubical lemma [3] in dimension n, in the form
of gist.RealCohesion.KuhnLemma: for every p and every labelling ℓ that
gives each point of the grid {0, …, p + 1}ⁿ a vector of n bits, such
that the i-th bit is ₀ on the face where the i-th coordinate is 0 and
₁ on the face where it is p + 1, some unit cube of the grid has, for
every i, a corner whose i-th bit is ₀ and a corner whose i-th bit is
₁. The corners of the unit cube at q are corner q r, for r : Fin n → 𝟚.
The statement depends on the function bit from 𝟚 to ℕ only through
corner, so it is stated for any such function (Kuhn-Lemma-with), and
Kuhn-Lemma is the instance for bit.

The five definitions below are those of gist.RealCohesion.KuhnLemma in
the frozen delivery r3 (lines 75–97 there), moved here unchanged. They
used to be defined twice, there and in
gist.RealCohesion.BrouwerStatements, with two different functions bit,
and gist.RealCohesion.Theorems transported between the two statements.
Now both modules name these definitions by typed aliases, which keep
their names, types and module parameters and unfold to the same
constants, so that both modules state the lemma with these constants.
This module uses neither --cohesion nor real numbers, so that plain
and cohesive modules can import it, and it contains no proof.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K2.
    references/F02-consolidation-plan.md

[2] GPT-6 Astra. Consolidation implementation, first release,
    13 November 2026.
    references/A26-consolidation-release-01.txt

[3] Harold W. Kuhn. Some combinatorial lemmas in topology. IBM Journal
    of Research and Development 4(5), 518–524, 1960.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.KuhnStatement where

open import MLTT.Spartan
open import Fin.Type
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.Order

corner-with : (𝟚 → ℕ) → {n : ℕ} → (Fin n → ℕ) → (Fin n → 𝟚) → Fin n → ℕ
corner-with b q r i = q i +ℕ b (r i)

Kuhn-Lemma-with : (𝟚 → ℕ) → ℕ → 𝓤₀ ̇
Kuhn-Lemma-with b n =
   (p : ℕ) (ℓ : (Fin n → ℕ) → Fin n → 𝟚)
 → ((a : Fin n → ℕ) → ((j : Fin n) → a j ≤ succ p)
        → (i : Fin n) → a i ＝ 0 → ℓ a i ＝ ₀)
 → ((a : Fin n → ℕ) → ((j : Fin n) → a j ≤ succ p)
        → (i : Fin n) → a i ＝ succ p → ℓ a i ＝ ₁)
 → Σ q ꞉ (Fin n → ℕ) , ((i : Fin n) → q i ≤ p)
     × ((i : Fin n) → Σ r ꞉ (Fin n → 𝟚) , Σ s ꞉ (Fin n → 𝟚)
           , (ℓ (corner-with b q r) i ＝ ₀) × (ℓ (corner-with b q s) i ＝ ₁))

bit : 𝟚 → ℕ
bit ₀ = 0
bit ₁ = 1

corner : {n : ℕ} → (Fin n → ℕ) → (Fin n → 𝟚) → Fin n → ℕ
corner = corner-with bit

Kuhn-Lemma : ℕ → 𝓤₀ ̇
Kuhn-Lemma = Kuhn-Lemma-with bit

\end{code}
