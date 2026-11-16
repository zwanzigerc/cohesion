Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

A real number that is positive exactly when some term of a given
sequence of real numbers is positive: the real-analytic part of
Lemma 4.1 of the write-up [1], gate G12 of Claude Fable 5.2's
blueprint addendum [2, §6, D1].

The exact statement. Lemma 4.1: assume Axiom T; then for every
sequence x of real numbers the proposition ∃ k , 0 < x k is
codiscrete. Its proof gives a real number m with 0 < m if and only if
∃ k , 0 < x k, and applies Axiom T to m.

The formal statement here is that equivalence,
sum-is-positive-iff-some-term-is, for every sequence and with no
hypothesis. Lemma 4.1 itself is
Axiom-T-gives-positive-terms-are-codiscrete of
gist.RealCohesion.AxiomTObstruction, and it is the target Target-4-1
in gist.RealCohesion.Theorems, for the native ♯.

The construction. The k-th term is x k clamped to [0 , 2⁻⁽ᵏ⁺²⁾], and
m is the sum of the terms. The write-up and the addendum clamp x k to
[0 , 1] and halve it k + 1 times; clamping to the smaller interval has
the same effect and needs no multiplication of real numbers. The
partial sums increase by at most 2⁻⁽ᵏ⁺²⁾ at step k, so they have a
limit m, within 2⁻⁽ᴺ⁺¹⁾ of the N-th partial sum
(gist.RealCohesion.RealLimits).

 * If 0 < x k, the k-th term is positive and every later partial sum
   is at least the k-th term, so 0 < m.

 * If 0 < m, some partial sum is positive. A positive finite sum has a
   positive term, and a positive term has 0 < x k.

No excluded middle and no choice are used.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    Lemma 4.1 and its proof.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Claude Fable 5.2. Formalization blueprint, addendum, revision 4 of
    11 November 2026.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.PositiveTerms
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order using (≤-+ ; ≤-+')
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic
 using (monotone-from-steps ; neg-is-negative)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ)
open import gist.RealCohesion.RealLattice fe pe pt
 using (min ; clamp ; clamp-is-above-lo ; clamp-is-below-hi ; ιₐ-≤-ιₐ ; sum-≤ ;
         ℝ≤-refl ;
        plus-zero ; zero-plus ; 0ℝ-below-positive⁻¹ ; positive-from-below ;
         ιₐ-positive ;
        ιₐ-zero-is-not-positive ; positive-sum ; positive-max ;
         positive-max-right ;
        positive-min ; positive-min⁻¹)
 renaming (_+_ to _ℝ+_)
open import gist.RealCohesion.RealLimits fe pe pt
 using
  (ρ ; ρ-is-positive ; ρ-is-nonneg ; ρ-antitone ; ρ-becomes-small ; within ;
   within-from-bounds ; module geometric-limit)

open PropositionalTruncation pt

\end{code}

The terms and the partial sums.

\begin{code}

module _ (x : ℕ → ℝ) where

 term : ℕ → ℝ
 term k = clamp (ιₐ 0ℚ) (ιₐ (ρ (succ k))) (x k)

 partial-sum : ℕ → ℝ
 partial-sum 0        = ιₐ 0ℚ
 partial-sum (succ k) = partial-sum k ℝ+ term k

 term-is-nonneg : (k : ℕ) → ιₐ 0ℚ ≤ term k
 term-is-nonneg k = clamp-is-above-lo (ιₐ 0ℚ) (ιₐ (ρ (succ k))) (x k)

 term-is-small : (k : ℕ) → term k ≤ ιₐ (ρ (succ k))
 term-is-small k = clamp-is-below-hi (ιₐ 0ℚ) (ιₐ (ρ (succ k))) (x k)
                    (ιₐ-≤-ιₐ 0ℚ (ρ (succ k)) (ρ-is-nonneg (succ k)))

 positive-term : (k : ℕ) → 0ℝ < x k → 0ℝ < term k
 positive-term k l =
  positive-max-right (ιₐ 0ℚ) (min (ιₐ (ρ (succ k))) (x k))
   (positive-min (ιₐ (ρ (succ k))) (x k)
     (ιₐ-positive (ρ (succ k)) (ρ-is-positive (succ k))) l)

 positive-term⁻¹ : (k : ℕ) → 0ℝ < term k → 0ℝ < x k
 positive-term⁻¹ k l =
  ∥∥-rec (<-is-prop 0ℝ (x k)) γ
   (positive-max (ιₐ 0ℚ) (min (ιₐ (ρ (succ k))) (x k)) l)
  where
   γ : (0ℝ < ιₐ 0ℚ) ∔ (0ℝ < min (ιₐ (ρ (succ k))) (x k)) → 0ℝ < x k
   γ (inl m) = 𝟘-elim (ιₐ-zero-is-not-positive m)
   γ (inr m) = pr₂ (positive-min⁻¹ (ιₐ (ρ (succ k))) (x k) m)

 sums-increase : (k : ℕ) → partial-sum k ≤ partial-sum (succ k)
 sums-increase k =
  transport (_≤ partial-sum (succ k)) (plus-zero (partial-sum k))
                    (sum-≤ (partial-sum k) (partial-sum k) (ιₐ 0ℚ) (term k)
                      (ℝ≤-refl (partial-sum k)) (term-is-nonneg k))

 sums-are-monotone : (k l : ℕ) → k ≤ l → partial-sum k ≤ partial-sum l
 sums-are-monotone =
  monotone-from-steps _≤_ ℝ≤-refl ℝ≤-trans partial-sum sums-increase

 term-below-sum : (k : ℕ) → term k ≤ partial-sum (succ k)
 term-below-sum k = transport (_≤ partial-sum (succ k)) (zero-plus (term k))
                     (sum-≤ (ιₐ 0ℚ) (partial-sum k) (term k) (term k)
                       (sums-are-monotone 0 k ⋆) (ℝ≤-refl (term k)))

 step : (k : ℕ) → within (ρ (succ k)) (partial-sum k) (partial-sum (succ k))
 step k =
  within-from-bounds (ρ (succ k)) (partial-sum k) (partial-sum (succ k)) I II
  where
   I : (partial-sum k ℝ+ ιₐ (ℚ- ρ (succ k))) ≤ partial-sum (succ k)
   I = sum-≤ (partial-sum k) (partial-sum k) (ιₐ (ℚ- ρ (succ k))) (term k)
        (ℝ≤-refl (partial-sum k))
        (ℝ≤-trans (ιₐ (ℚ- ρ (succ k))) (ιₐ 0ℚ) (term k)
          (ιₐ-≤-ιₐ (ℚ- ρ (succ k)) 0ℚ
            (ℚ<-coarser-than-≤ (ℚ- ρ (succ k)) 0ℚ
              (neg-is-negative (ρ (succ k)) (ρ-is-positive (succ k)))))
          (term-is-nonneg k))

   II : partial-sum (succ k) ≤ (partial-sum k ℝ+ ιₐ (ρ (succ k)))
   II = sum-≤ (partial-sum k) (partial-sum k) (term k) (ιₐ (ρ (succ k)))
         (ℝ≤-refl (partial-sum k)) (term-is-small k)

\end{code}

The sum, and the equivalence.

\begin{code}

 sum : ℝ
 sum = geometric-limit.lim partial-sum step

 sum-is-near : (N : ℕ) → within (ρ N) sum (partial-sum N)
 sum-is-near = geometric-limit.lim-within partial-sum step

 positive-sum-has-positive-term : (N : ℕ) → 0ℝ < partial-sum N
                                → ∃ k ꞉ ℕ , 0ℝ < term k
 positive-sum-has-positive-term 0        l = 𝟘-elim (ιₐ-zero-is-not-positive l)
 positive-sum-has-positive-term (succ N) l =
  ∥∥-rec ∃-is-prop γ (positive-sum (partial-sum N) (term N) l)
  where
   γ : (0ℝ < partial-sum N) ∔ (0ℝ < term N) → ∃ k ꞉ ℕ , 0ℝ < term k
   γ (inl m) = positive-sum-has-positive-term N m
   γ (inr m) = ∣ N , m ∣

 sum-is-positive-iff-some-term-is : (0ℝ < sum) ↔ (∃ k ꞉ ℕ , 0ℝ < x k)
 sum-is-positive-iff-some-term-is = I , II
  where
   I : 0ℝ < sum → ∃ k ꞉ ℕ , 0ℝ < x k
   I = ∥∥-rec ∃-is-prop γ
    where
     γ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < sum)) → ∃ k ꞉ ℕ , 0ℝ < x k
     γ (q , m , n) = ∥∥-functor δ (positive-sum-has-positive-term N III)
      where
       small : Σ N ꞉ ℕ , ρ N < q
       small = ρ-becomes-small q (0ℝ-below-positive⁻¹ q m)

       N : ℕ
       N = pr₁ small

       III : 0ℝ < partial-sum N
       III = positive-from-below (partial-sum N) (q ℚ- ρ N)
              (ℚ<-difference-positive (ρ N) q (pr₂ small))
              (pr₁ (sum-is-near N) q n)

       δ : (Σ k ꞉ ℕ , 0ℝ < term k) → Σ k ꞉ ℕ , 0ℝ < x k
       δ (k , o) = k , positive-term⁻¹ k o

   II : (∃ k ꞉ ℕ , 0ℝ < x k) → 0ℝ < sum
   II = ∥∥-rec (<-is-prop 0ℝ sum) γ
    where
     γ : (Σ k ꞉ ℕ , 0ℝ < x k) → 0ℝ < sum
     γ (k , l) = ∥∥-rec (<-is-prop 0ℝ sum) δ (positive-term k l)
      where
       δ : (Σ q ꞉ ℚ , (0ℝ < q) × (q < term k)) → 0ℝ < sum
       δ (q , m , n) = positive-from-below sum (q ℚ- ρ M)
                        (ℚ<-difference-positive (ρ M) q IV)
                         (pr₂ (sum-is-near M) q V)
        where
         small : Σ d ꞉ ℕ , ρ d < q
         small = ρ-becomes-small q (0ℝ-below-positive⁻¹ q m)

         d : ℕ
         d = pr₁ small

         M : ℕ
         M = d +ℕ succ k

         IV : ρ M < q
         IV =
          ℚ≤-<-trans (ρ M) (ρ d) q (ρ-antitone d M (≤-+ d (succ k))) (pr₂ small)

         V : q < partial-sum M
         V = ℝ≤-trans (term k) (partial-sum (succ k)) (partial-sum M)
              (term-below-sum k)
               (sums-are-monotone (succ k) M (≤-+' d (succ k))) q n

\end{code}
