Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026; moved to this module on 11 November 2026.
See the AI disclosure in gist.RealCohesion.index.

The heights, parity and plateaus shared by sequential hitting
(gist.RealCohesion.SequentialHitting), the plateau path
(gist.RealCohesion.PlateauPath) and the modules built on them.

 * The heights hgt n = ρ (n + 3) = 2⁻⁽ⁿ⁺⁴⁾. The plateau path through a
   sequence q needs q n within hgt n of its base point.

 * Parity on ℕ, for sequences that alternate between two kinds of
   terms.

 * The plateaus (α j , β j) of the finite-chain lemma
   (gist.RealCohesion.FiniteChainLemma), with α j = 5/8 · 2⁻ʲ, midpoint
   m j = 3/4 · 2⁻ʲ and β j = 7/8 · 2⁻ʲ.

These are lemmas for the proofs of Theorems 7.4 and 7.10 of the
write-up [1], not statements of it. The code is moved unchanged from
gist.RealCohesion.SequentialHitting, which re-exports it, so that
gist.RealCohesion.SequentialHitting can take its path from
gist.RealCohesion.PlateauPath without a circular import.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.Plateaus
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order hiding (max)
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import gist.RealCohesion.RationalArithmetic using (<-sub-right)
open import gist.RealCohesion.RationalArithmetic using (neg-is-negative) public
open import gist.RealCohesion.RealLimits fe pe pt
 using
  (ρ ; ρ-is-positive ; ρ-decreases ; ρ-halves ; ρ-shift ; ρ-is-at-most-a-half ;
   ℚ<-add-left)
open import gist.RealCohesion.RealLimits fe pe pt using (ρ-antitone) public
open import gist.RealCohesion.FiniteChainLemma fe pe pt
 using (odd-index ; even-index)

\end{code}

The heights hgt n = ρ (n + 3) = 2⁻⁽ⁿ⁺⁴⁾, and facts about ρ.

\begin{code}

hgt : ℕ → ℚ
hgt n = ρ (n +ℕ 3)

hgt-is-positive : (n : ℕ) → 0ℚ < hgt n
hgt-is-positive n = ρ-is-positive (n +ℕ 3)

hgt-is-small : (n : ℕ) → hgt n ≤ ρ 3
hgt-is-small n =
 transport (λ k → ρ k ≤ ρ 3) (addition-commutativity 3 n) (ρ-shift 3 n)

hgt-below-ρ : (n : ℕ) → hgt n ≤ ρ n
hgt-below-ρ n = ρ-shift n 3

ρ-double-below : (i j : ℕ) → succ i ≤ℕ j → ρ j ℚ+ ρ j ≤ ρ i
ρ-double-below i 0        l = 𝟘-elim l
ρ-double-below i (succ j) l =
 transport (_≤ ρ i) (ρ-halves j ⁻¹) (ρ-antitone i j l)

\end{code}

Parity.

\begin{code}

parity : ℕ → 𝟚
parity 0        = ₀
parity (succ n) = complement (parity n)

parity-of-odd-index : (k : ℕ) → parity (odd-index k) ＝ ₁
parity-of-odd-index 0        = refl
parity-of-odd-index (succ k) = complement-involutive (parity (odd-index k))
                               ∙ parity-of-odd-index k

parity-of-even-index : (k : ℕ) → parity (even-index k) ＝ ₀
parity-of-even-index k = ap complement (parity-of-odd-index k)

odd-pred : ℕ → ℕ
odd-pred 0        = 0
odd-pred (succ k) = succ (odd-index k)

odd-index-is-succ : (k : ℕ) → odd-index k ＝ succ (odd-pred k)
odd-index-is-succ 0        = refl
odd-index-is-succ (succ k) = refl

\end{code}

The plateaus of the finite-chain lemma: α j = 5/8 · 2⁻ʲ,
m j = 3/4 · 2⁻ʲ, β j = 7/8 · 2⁻ʲ, written with ρ j = 2⁻⁽ʲ⁺¹⁾.

\begin{code}

α m β : ℕ → ℚ
α j = ρ j ℚ+ ρ (succ (succ j))
m j = ρ j ℚ+ ρ (succ j)
β j = (ρ j ℚ+ ρ j) ℚ- ρ (succ (succ j))

α-below-m : (j : ℕ) → α j < m j
α-below-m j =
 ℚ<-add-left (ρ j) (ρ (succ (succ j))) (ρ (succ j)) (ρ-decreases (succ j))

m-below-β : (j : ℕ) → m j < β j
m-below-β j = <-sub-right (m j) (ρ j ℚ+ ρ j) (ρ (succ (succ j))) I
 where
  I : m j ℚ+ ρ (succ (succ j)) < ρ j ℚ+ ρ j
  I = transport₂ _<_
       (ℚ+-assoc (ρ j) (ρ (succ j)) (ρ (succ (succ j))) ⁻¹)
       (ap (ρ j ℚ+_) (ρ-halves j))
       (ℚ<-add-left (ρ j) (ρ (succ j) ℚ+ ρ (succ (succ j)))
         (ρ (succ j) ℚ+ ρ (succ j))
         (ℚ<-add-left (ρ (succ j)) (ρ (succ (succ j))) (ρ (succ j))
           (ρ-decreases (succ j))))

m-decreases : (j : ℕ) → m (succ j) < m j
m-decreases j = ℚ<-adding (ρ (succ j)) (ρ j) (ρ (succ (succ j))) (ρ (succ j))
                 (ρ-decreases j) (ρ-decreases (succ j))

m-is-positive : (j : ℕ) → 0ℚ < m j
m-is-positive j =
 ℚ<-adding-zero (ρ j) (ρ (succ j)) (ρ-is-positive j) (ρ-is-positive (succ j))

m-below-1 : (j : ℕ) → m j < 1ℚ
m-below-1 j = ℚ<-≤-trans (m j) (ρ j ℚ+ ρ j) 1ℚ
               (ℚ<-add-left (ρ j) (ρ (succ j)) (ρ j) (ρ-decreases j))
               (transport (ρ j ℚ+ ρ j ≤_) 1/2+1/2
                 (ℚ≤-adding (ρ j) 1/2 (ρ j) 1/2 (ρ-is-at-most-a-half j)
                   (ρ-is-at-most-a-half j)))

β-below-double : (j : ℕ) → β j < ρ j ℚ+ ρ j
β-below-double j =
 ℚ<-subtraction-preserves-order (ρ j ℚ+ ρ j) (ρ (succ (succ j)))
                    (ρ-is-positive (succ (succ j)))

ρ-below-α : (j : ℕ) → ρ j < α j
ρ-below-α j = ℚ<-addition-preserves-order'' (ρ j) (ρ (succ (succ j)))
               (ρ-is-positive (succ (succ j)))

\end{code}
