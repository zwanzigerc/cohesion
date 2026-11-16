Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time); one sentence updated
13 November 2026, after the final audits; the lemmas moved to
gist.CohesiveApartness on 13 November 2026, in the consolidation that
followed. Orbifold gate H8 of Fable's roadmap [1], after the review
dated 13 November 2026 (UTC) [2, 3].

Crisp elimination of propositional truncations
----------------------------------------------

For a crisp type A, a crisp element of ∥ A ∥ gives an element of
∥ ♭ A ∥, with the native ♯ of Agda 2.9.0 and no axiom. So, to prove a
proposition P, which may be ordinary and may depend on ordinary
variables, a crisp mere element of A may be replaced by a crisp
element:

  crisp-∥∥-rec : is-prop P → ((@♭ a : A) → P) → (@♭ t : ∥ A ∥) → P.

This is obligation 1 of Fable's note [2, Section 1], with the scope
checked by GPT-6 Astra [3, Section 1]: A and its universe are crisp;
P, its universe, its propositionality and the handler need not be.
The bridges in MyersMicrolinearity open the four crisp mere
presentations of a crisp square with it, one after the other.

Source. The proofs are those of Claude Fable 5.2's scratch check
CrispTruncationCheck.lagda of 13 November 2026 (SHA-256
59a924f45f9f2ffc7e558b67e574fad2163ce1305b20100229bd8f6d5e4b8733, in
provenance/companions/orbifolds-readiness-2026-11-13/),
code of this project and not an external source. They were adapted
only in the module name and header; the nested form for four elements
is not kept, since the bridges nest the eliminator directly.

On 13 November 2026, in the consolidation after the final audits
(step K1 of Claude Fable 5.2's consolidation plan [4], released by
GPT-6 Astra [5]), the five lemmas moved unchanged to two modules
beside the native ♯, since they are not about orbifolds: the first
two, which repeated lemmas of
gist.RealCohesion.BoundaryRetractionFromC1Targets, to
gist.CohesiveApartness.SharpProperties, and the other three to
gist.CohesiveApartness.CrispTruncation. This module keeps the five
names, with their types and the parameters of this module, as typed
aliases, so that its importers are unchanged.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds: the two statement bridges of H8, and
    readiness for H9 and H10, 13 November 2026, Section 1.
    references/F05-orbifolds-h8-bridges.md
[3] GPT-6 Astra. Fable's H8 answer: bridges, crisp truncation, and T2,
    13 November 2026, Section 1.
    references/A14-h8-answer-audit.txt
[4] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K1.
    references/F02-consolidation-plan.md
[5] GPT-6 Astra. Consolidation implementation, first release,
    13 November 2026.
    references/A26-consolidation-release-01.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.Orbifolds.CrispTruncation
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import gist.CohesiveApartness.Sharp
import gist.CohesiveApartness.SharpProperties
import gist.CohesiveApartness.CrispTruncation

open PropositionalTruncation pt

private
 module SP = gist.CohesiveApartness.SharpProperties fe
 module CT = gist.CohesiveApartness.CrispTruncation fe pt

identifications-in-♯-from-sharp-ones
 : {𝓤 : Universe} {A : 𝓤 ̇ } (u v : ♯ A) → ♯ (u ＝ v) → u ＝ v
identifications-in-♯-from-sharp-ones = SP.identifications-in-♯-from-sharp-ones

♯-of-a-proposition-is-a-proposition
 : {𝓤 : Universe} {G : 𝓤 ̇ } → is-prop G → is-prop (♯ G)
♯-of-a-proposition-is-a-proposition = SP.♯-of-a-proposition-is-a-proposition

truncation-into-♯ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } → ∥ A ∥ → ♯ ∥ ♭ A ∥
truncation-into-♯ = CT.truncation-into-♯

crisp-truncations-give-truncations-of-♭
 : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } (@♭ t : ∥ A ∥) → ∥ ♭ A ∥
crisp-truncations-give-truncations-of-♭ =
 CT.crisp-truncations-give-truncations-of-♭

crisp-∥∥-rec : {@♭ 𝓤 : Universe} {𝓥 : Universe} {@♭ A : 𝓤 ̇ } {P : 𝓥 ̇ }
             → is-prop P
             → ((@♭ a : A) → P)
             → (@♭ t : ∥ A ∥) → P
crisp-∥∥-rec = CT.crisp-∥∥-rec

\end{code}
