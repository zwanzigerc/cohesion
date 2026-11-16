Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; prose adapted to this folder by Claude
Opus 5.5 on the same day. See the AI disclosure in
gist.RealCohesion.index.

The statements of the approximate intermediate value theorem from
Axiom R♭ alone, as they were fixed before the formalization started,
in the starter module of the formalization blueprint [1]. This module
has only the statements; gist.RealCohesion.ApproximateIVT proves them.

Approximate-IVT is crisp-approximate-IVT of
gist.RealCohesion.CrispDiscreteness with every crispness annotation
removed. Normal-Form is the statement that the analytic part of the
proof establishes; the blueprint reduces Approximate-IVT to it. The
theorem is

  Singly-Generated-Punctual-Cohesion ℝ 0ℝ → Approximate-IVT

with Singly-Generated-Punctual-Cohesion from
gist.CohesiveApartness.Flat.

Sequential-Hitting is the lemma of GPT-6 Astra around which revision 3
of the blueprint is organized: if h a is at least 1 and z j is within
2⁻ʲ of a for every j, then h is positive at some z j. It also follows
from Axiom R♭ alone, and the normal form is derived from it. The bound
|z j - a| ≤ 2⁻ʲ is stated as two inequalities, so that no absolute
value is needed.

[1] Formalization blueprint: the approximate IVT from Axiom R♭.
    Claude Fable 5.2, revision 3, 10 November 2026.
    references/F15-aivt-blueprint-rev3.md
    references/F16-aivt-handoff-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.ApproximateIVTStatement
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Fractions
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Addition fe pe pt renaming (_+_ to _+ℝ_)
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)

open PropositionalTruncation pt

Approximate-IVT : 𝓤₁ ̇
Approximate-IVT = (f : ℝ → ℝ) (p q a b : ℝ)
                → p < q
                → f a < q
                → p < f b
                → ∃ x ꞉ ℝ , (p < f x) × (f x < q)

Normal-Form : ℚ → ℚ → 𝓤₁ ̇
Normal-Form one-third two-thirds =
   (g : ℝ → ℝ)
 → g 0ℝ ≤ embedding-ℚ-to-ℝ one-third
 → embedding-ℚ-to-ℝ two-thirds ≤ g 1ℝ
 → ∃ x ꞉ ℝ , (0ℝ < g x) × (g x < 1ℝ)

2⁻ : ℕ → ℝ
2⁻ j = embedding-ℚ-to-ℝ (⟨1/2⟩^ j)

Sequential-Hitting : 𝓤₁ ̇
Sequential-Hitting =
   (h : ℝ → ℝ) (a : ℝ) (z : ℕ → ℝ)
 → ((j : ℕ) → (z j ≤ a +ℝ 2⁻ j) × (a ≤ z j +ℝ 2⁻ j))
 → 1ℝ ≤ h a
 → ∃ j ꞉ ℕ , 0ℝ < h (z j)

\end{code}
