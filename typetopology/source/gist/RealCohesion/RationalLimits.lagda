Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Bounds for repeated halving, in terms of the powers of 2/3 of
Rationals.Limits.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RationalLimits
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import UF.Base
open import Rationals.Limits fe pe pt
open import Rationals.Multiplication
open import Rationals.Order
open import Rationals.Type
open import gist.RealCohesion.RationalArithmetic

\end{code}

A bound for repeated halving.

\begin{code}

halving-bound : (y d : ℚ)
              → 0ℚ ≤ y
              → (n : ℕ)
              → d ≤ (⟨2/3⟩^ n) * y
              → half d ≤ (⟨2/3⟩^ (succ n)) * y
halving-bound y d y-nonneg n l =
 ℚ≤-trans (half d) ((a * y) * 1/2) ((⟨2/3⟩^ (succ n)) * y)
  I (transport ((a * y) * 1/2 ≤_) III' II)
 where
  a : ℚ
  a = ⟨2/3⟩^ n

  a-nonneg : 0ℚ ≤ a
  a-nonneg = ⟨2/3⟩-all-positive n

  ay-nonneg : 0ℚ ≤ a * y
  ay-nonneg = ℚ≤-pos-multiplication-preserves-order a y a-nonneg y-nonneg

  I : half d ≤ (a * y) * 1/2
  I = ℚ≤-pos-multiplication-preserves-order' d (a * y) 1/2 l 0≤1/2

  II : (a * y) * 1/2 ≤ (a * y) * 2/3
  II = transport₂ _≤_ (ℚ*-comm 1/2 (a * y)) (ℚ*-comm 2/3 (a * y))
        (ℚ≤-pos-multiplication-preserves-order' 1/2 2/3 (a * y) 1/2≤2/3
          ay-nonneg)

  III : (a * y) * 2/3 ＝ (a * 2/3) * y
  III = ℚ*-assoc a y 2/3 ∙ ap (a *_) (ℚ*-comm y 2/3) ∙ ℚ*-assoc a 2/3 y ⁻¹

  III' : (a * y) * 2/3 ＝ (⟨2/3⟩^ (succ n)) * y
  III' = III ∙ ap (_* y) (⟨2/3⟩-to-mult n ⁻¹)

\end{code}

The bounds of a halving sequence (gist.RealCohesion.RationalArithmetic)
by powers of 2/3, and that it becomes arbitrarily small.

\begin{code}

module halving-sequence-bounds
        (x : ℕ → ℚ)
        (x-succ : (n : ℕ) → x (succ n) ＝ half (x n))
        (c : ℚ)
        (c-is-nonneg : 0ℚ ≤ c)
        (x-zero-bound : x 0 ≤ c)
       where

 bound : (n : ℕ) → x n ≤ (⟨2/3⟩^ n) * c
 bound 0        = transport (x 0 ≤_) (ℚ-mult-left-id c ⁻¹) x-zero-bound
 bound (succ n) = transport (_≤ (⟨2/3⟩^ (succ n)) * c) (x-succ n ⁻¹)
                   (halving-bound c (x n) c-is-nonneg n (bound n))

 becomes-small : (ε : ℚ) → 0ℚ < ε → Σ n ꞉ ℕ , x n < ε
 becomes-small ε l = δ (ℚ-dichotomous' 0ℚ c)
  where
   γ : (Σ n ꞉ ℕ , (⟨2/3⟩^ n) * c < ε) → Σ n ꞉ ℕ , x n < ε
   γ (n , k) = n , ℚ≤-<-trans (x n) ((⟨2/3⟩^ n) * c) ε (bound n) k

   δ : (0ℚ < c) ∔ (c ≤ 0ℚ) → Σ n ꞉ ℕ , x n < ε
   δ (inl m) = γ (⟨2/3⟩^n<ε-consequence (ε , l) (c , m))
   δ (inr m) = 0 , ℚ≤-<-trans (x 0) 0ℚ ε (ℚ≤-trans (x 0) c 0ℚ x-zero-bound m) l

\end{code}
