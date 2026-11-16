Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Countable choice for crisp families of arbitrary types: if every type
B n of a crisp family is inhabited, crisply, then merely so is their
product.

This is the case of the crisp ♭-discrete set ℕ of Shulman's discrete
axiom of choice [1, Theorem 6.30], which he derives from his Axiom AC.
The types B n are arbitrary, not only sets, as needed for identity
types of the shape of a set, which may have higher structure. It is
derived from the discrete axiom of choice of
gist.RealCohesion.CrispDiscreteness in gist.RealCohesion.FlatSplit,
where ℕ is shown to be ♭-discrete.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.PropTrunc

module gist.RealCohesion.CrispCountableChoice
        (@♭ pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

Crisp-Countable-Choice : (@♭ 𝓦 : Universe) → 𝓦 ⁺ ̇
Crisp-Countable-Choice 𝓦 = (@♭ B : ℕ → 𝓦 ̇ )
                          → @♭ ((n : ℕ) → ∥ B n ∥)
                          → ∥ ((n : ℕ) → B n) ∥

\end{code}
