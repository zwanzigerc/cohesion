Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Sequential hitting along a pair of sequences.

Let H : ℝ → ℝ → ℝ be any function of two real variables, x a real
number with 1 ≤ H x x, and y, y' two sequences with y j and y' j within
2⁻⁽ʲ⁺¹⁾ of x. If every map ℝ → Q is constant, then 0 < H (y n) (y' n)
for some n. This is sequential hitting for functions on ℝ², which
GPT-6 Astra's proof of rational detection uses [1, §3].

It is the instance X = 𝟚 of sequential hitting for functionals
(gist.RealCohesion.FunctionalHitting), with h f = H (f ₀) (f ₁). This
module first proved it by a reduction to one variable, through a path
through each sequence. That reduction, for any family of sequences, is
now in gist.RealCohesion.FunctionalHitting, and the two lemmas it used
are in gist.RealCohesion.PlateauPath (ψ-at-zero) and
gist.RealCohesion.RealLimits (within-zero).

[1] GPT-6 Astra. Positive rational detection, 10 November 2026.
    references/A11-positive-rational-detection.txt

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.PairHitting
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import Rationals.Type
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt using (ρ ; within)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FunctionalHitting fe pe pt
 using (functional-hitting)

open PropositionalTruncation pt

\end{code}

Sequential hitting along a pair of sequences.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 pair-hitting : (H : ℝ → ℝ → ℝ) (x : ℝ) (y y' : ℕ → ℝ)
              → ((j : ℕ) → within (ρ j) (y j) x)
              → ((j : ℕ) → within (ρ j) (y' j) x)
              → ιₐ 1ℚ ≤ H x x
              → ∃ n ꞉ ℕ , 0ℚ < H (y n) (y' n)
 pair-hitting H x y y' c c' = functional-hitting ν h (λ _ → x) z close
  where
   h : (𝟚 → ℝ) → ℝ
   h f = H (f ₀) (f ₁)

   z : ℕ → 𝟚 → ℝ
   z j ₀ = y j
   z j ₁ = y' j

   close : (j : ℕ) (b : 𝟚) → within (ρ j) (z j b) x
   close j ₀ = c j
   close j ₁ = c' j

\end{code}
