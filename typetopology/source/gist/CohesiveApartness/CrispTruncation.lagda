Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: step K1 of Claude Fable 5.2's plan [1], as
released by GPT-6 Astra [2]. See the AI disclosure in
gist.CohesiveApartness.index.

Crisp elimination of propositional truncations
----------------------------------------------

For a crisp type A, a crisp element of ∥ A ∥ gives an element of
∥ ♭ A ∥, with the native ♯ of Agda 2.9.0 and no axiom. So, to prove a
proposition P, which may be ordinary and may depend on ordinary
variables, a crisp mere element of A may be replaced by a crisp
element:

  crisp-∥∥-rec : is-prop P → ((@♭ a : A) → P) → (@♭ t : ∥ A ∥) → P.

A and its universe are crisp; P, its universe, its propositionality
and the handler need not be. The proof maps ∥ A ∥ into the proposition
♯ ∥ ♭ A ∥ (truncation-into-♯), with
gist.CohesiveApartness.SharpProperties, and eliminates ♯ on the crisp
image of t.

Source. These are the last three lemmas of gist.Orbifolds.CrispTruncation
in the frozen delivery r3 (its lines 76–96), whose proofs are those of
Claude Fable 5.2's scratch check CrispTruncationCheck.lagda of
13 November 2026, code of this project. They are moved here unchanged,
since they are not about orbifolds; gist.Orbifolds.CrispTruncation now
names them by typed aliases. As there, function extensionality and the
propositional truncations are crisp parameters: the crisp elimination
of ♯ in crisp-truncations-give-truncations-of-♭ needs them crisp.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K1.
    references/F02-consolidation-plan.md

[2] GPT-6 Astra. Consolidation implementation, first release,
    13 November 2026.
    references/A26-consolidation-release-01.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.CohesiveApartness.CrispTruncation
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import gist.CohesiveApartness.Sharp
open import gist.CohesiveApartness.SharpProperties fe
 using (♯-of-a-proposition-is-a-proposition)

open PropositionalTruncation pt

truncation-into-♯ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } → ∥ A ∥ → ♯ ∥ ♭ A ∥
truncation-into-♯ {𝓤} {A} =
 ∥∥-rec (♯-of-a-proposition-is-a-proposition ∥∥-is-prop) g
 where
  g : A → ♯ ∥ ♭ A ∥
  g a .ε♯ = ∣ a ^♭ ∣

crisp-truncations-give-truncations-of-♭
 : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } (@♭ t : ∥ A ∥) → ∥ ♭ A ∥
crisp-truncations-give-truncations-of-♭ t =
 crisp-elim-sharp (truncation-into-♯ t)

crisp-∥∥-rec : {@♭ 𝓤 : Universe} {𝓥 : Universe} {@♭ A : 𝓤 ̇ } {P : 𝓥 ̇ }
             → is-prop P
             → ((@♭ a : A) → P)
             → (@♭ t : ∥ A ∥) → P
crisp-∥∥-rec {𝓤} {𝓥} {A} {P} i φ t =
 ∥∥-rec i γ (crisp-truncations-give-truncations-of-♭ t)
 where
  γ : ♭ A → P
  γ (a ^♭) = φ a

\end{code}
