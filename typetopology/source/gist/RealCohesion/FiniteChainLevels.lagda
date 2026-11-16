Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; prose adapted to this folder by Claude
Opus 5.5 on the same day. See the AI disclosure in
gist.RealCohesion.index.

Levels and finite chains.

A level is a binary sequence. We write x ⪯ y for "x ≤ y + 1" when
levels are read as extended natural numbers: if x has a 1 at position
k + 1 then y has a 1 at position k. Two levels are adjacent if each
is ⪯ the other. Along a chain of n adjacent steps starting from a
level with a 0 at position k, the last level has a 0 at position
k + n. In particular, a chain of length n from the zero level ends in
a level with a 0 at position n. This is Lemma 1.2 of the proof note
[1]. Together with the effectivity of the quotient of levels by
finite chains (gist.RealCohesion.FiniteChainQuotient), it turns an
equality in that quotient into a natural number.

The levels of [1] are decreasing binary sequences, that is, elements
of ℕ∞. Nothing in the argument uses that the levels are decreasing,
so we take all binary sequences, which makes the levels ♭-discrete
under Axiom R♭ by a pointwise argument
(gist.RealCohesion.FiniteChainDiscreteness).

[1] The approximate intermediate value theorem from real cohesion
    alone. Proof note by Claude Fable 5.2, revision 2, 10 November
    2026, audited by GPT-6 Astra.
    references/F17-aivt-proof-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.FiniteChainLevels where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Relations.SRTclosure

Level : 𝓤₀ ̇
Level = ℕ → 𝟚

_⪯_ : Level → Level → 𝓤₀ ̇
x ⪯ y = (k : ℕ) → x (succ k) ＝ ₁ → y k ＝ ₁

Adj : Level → Level → 𝓤₀ ̇
Adj x y = (x ⪯ y) × (y ⪯ x)

Adj-is-symmetric : symmetric Adj
Adj-is-symmetric x y (a , b) = b , a

zero-level : Level
zero-level _ = ₀

zeros-move-up-by-one
 : (x z : Level) (k : ℕ)
 → z ⪯ x
 → x k ＝ ₀
 → z (succ k) ＝ ₀
zeros-move-up-by-one x z k l e =
 different-from-₁-equal-₀ (λ p → zero-is-not-one (e ⁻¹ ∙ l k p))

chains-move-zeros-up-slowly
 : (n : ℕ) (x y : Level) (k : ℕ)
 → iteration Adj n x y
 → x k ＝ ₀
 → y (k +ℕ n) ＝ ₀
chains-move-zeros-up-slowly 0        x x k refl              e = e
chains-move-zeros-up-slowly (succ n) x y k (z , (_ , l) , c) e =
 transport (λ - → y - ＝ ₀) (succ-left k n)
  (chains-move-zeros-up-slowly n z y (succ k) c
    (zeros-move-up-by-one x z k l e))

chains-from-the-zero-level-end-with-a-zero
 : (n : ℕ) (x : Level)
 → iteration Adj n zero-level x
 → x n ＝ ₀
chains-from-the-zero-level-end-with-a-zero n x c =
 transport (λ - → x - ＝ ₀) (zero-left-neutral n)
  (chains-move-zeros-up-slowly n zero-level x 0 c refl)

\end{code}
