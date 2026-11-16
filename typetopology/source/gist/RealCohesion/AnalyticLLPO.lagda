Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Shulman's Theorem 11.7 without crisp excluded middle: Axiom R♭
refutes the analytic lesser limited principle of omniscience
(Theorem 7.10 of the write-up [2]).

Exact statement served. Theorem 7.10 of the write-up [2]: assume
Axiom R♭; it is not the case that x ≤ 0 or x ≥ 0 for every x : ℝ. The
formal statement R♭-refutes-analytic-LLPO : Target-7-10, in
gist.RealCohesion.Theorems, is identical to it, with Target-7-10 and
Analytic-LLPO as in gist.RealCohesion.BrouwerStatements. This module
proves it from the constancy of maps ℝ → Q (analytic-LLPO-fails);
gist.RealCohesion.Theorems bridges to Axiom R♭ through
gist.RealCohesion.FiniteChainDiscreteness.

The analytic LLPO says that every real number x has x ≤ 0 or 0 ≤ x.
Shulman refutes it from Axioms LEM and R♭ [1, Theorem 11.7]. Claude
Fable 5.2's proof [2, 3] uses Axiom R♭ alone, through the finite-chain
lemma (gist.RealCohesion.FiniteChainLemma). GPT-6 Astra audited it on
paper on 11 November 2026, relative to the finite-chain lemma [3]:

 * The zigzag q n is - 2⁻⁽ⁿ⁺⁴⁾ for odd n and 2⁻⁽ⁿ⁺⁴⁾ for even n, so
   q n is within hgt n = 2⁻⁽ⁿ⁺⁴⁾ of 0.

 * φ is the plateau path through q from 0
   (gist.RealCohesion.PlateauPath): φ s ＝ q j on the plateau of index
   j ≥ 1. So φ is negative on the odd plateaus and positive on the
   even ones.

 * If the analytic LLPO held, the sets A := {s | 0 ≤ φ s} and
   D := {s | φ s ≤ 0} would cover ℝ, A would miss the odd plateaus and
   D the even ones.

 * The finite-chain lemma, with the depth constantly ₀, would then give
   an index j with ₀ ＝ ₁.

As in gist.RealCohesion.SequentialHitting, we assume that every map
ℝ → Q is constant, which follows from Axiom R♭
(gist.RealCohesion.FiniteChainDiscreteness);
gist.RealCohesion.Theorems states the theorem from Axiom R♭.

The zigzag differs from that of the write-up, (-1)ʲ 2⁻ʲ, only in its
size: the plateau path of gist.RealCohesion.PlateauPath needs q n
within 2⁻⁽ⁿ⁺⁴⁾ of the base point. The signs are those of the
write-up.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    Theorem 7.10.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[3] Formalization blueprint, addendum: Theorem 7.10, Corollary 3.7,
    Theorem 4.3 and Theorem 8.32, revision 3, Part A. Claude Fable
    5.2, 11 November 2026.
    references/F14-brouwer-addendum-rev4.md
    (retained as revision 4, which states that it differs from
    revision 3 only by Part F and gate G15)

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.AnalyticLLPO
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import MLTT.Two-Properties
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
 using (within ; within-zero ; minus-nonneg-is-below ; minus-is-antitone)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FiniteChainLemma fe pe pt
 using (odd-index ; even-index ; module finite-chain-lemma)
open import gist.RealCohesion.Plateaus fe pe pt
 using (hgt ; hgt-is-positive ; neg-is-negative ; parity ; parity-of-odd-index ;
        parity-of-even-index ; odd-pred ; odd-index-is-succ ;
        α ; m ; β ; α-below-m ; m-below-β ; m-decreases ; m-is-positive ;
         m-below-1)
open import gist.RealCohesion.PlateauPath fe pe pt

open PropositionalTruncation pt

\end{code}

The analytic lesser limited principle of omniscience, as in
gist.RealCohesion.BrouwerStatements.

\begin{code}

Analytic-LLPO : 𝓤₁ ̇
Analytic-LLPO = (x : ℝ) → (x ≤ 0ℝ) ∨ (0ℝ ≤ x)

\end{code}

The zigzag, and its closeness to 0.

\begin{code}

within-zero⁻ : (ε u : ℚ) → 0ℚ < u → u ≤ ε → within ε (ιₐ (ℚ- u)) (ιₐ 0ℚ)
within-zero⁻ ε u l k = I , II
 where
  ε-is-nonneg : 0ℚ ≤ ε
  ε-is-nonneg = ℚ≤-trans 0ℚ u ε (ℚ<-coarser-than-≤ 0ℚ u l) k

  I : (p : ℚ) → p < ιₐ (ℚ- u) → (p ℚ- ε) < ιₐ 0ℚ
  I p o = ιₐ-lower (p ℚ- ε) 0ℚ
           (ℚ≤-<-trans (p ℚ- ε) p 0ℚ (minus-nonneg-is-below p ε ε-is-nonneg)
             (ℚ<-trans p (ℚ- u) 0ℚ (ιₐ-lower⁻¹ p (ℚ- u) o)
               (neg-is-negative u l)))

  II : (p : ℚ) → p < ιₐ 0ℚ → (p ℚ- ε) < ιₐ (ℚ- u)
  II p o = ιₐ-lower (p ℚ- ε) (ℚ- u)
            (ℚ≤-<-trans (p ℚ- ε) (p ℚ- u) (ℚ- u) (minus-is-antitone p u ε k)
              (transport (p ℚ- u <_) (ℚ-zero-left-neutral (ℚ- u))
                (ℚ<-addition-preserves-order p 0ℚ (ℚ- u) (ιₐ-lower⁻¹ p 0ℚ o))))

zigzag' : 𝟚 → ℕ → ℝ
zigzag' ₀ n = ιₐ (hgt n)
zigzag' ₁ n = ιₐ (ℚ- hgt n)

zigzag : ℕ → ℝ
zigzag n = zigzag' (parity n) n

zigzag-is-close : (n : ℕ) → within (hgt n) (zigzag n) (ιₐ 0ℚ)
zigzag-is-close n = γ (parity n)
 where
  γ : (b : 𝟚) → within (hgt n) (zigzag' b n) (ιₐ 0ℚ)
  γ ₀ = within-zero (hgt n) (hgt n) (hgt-is-positive n) (ℚ≤-refl (hgt n))
  γ ₁ = within-zero⁻ (hgt n) (hgt n) (hgt-is-positive n) (ℚ≤-refl (hgt n))

\end{code}

The plateau path through the zigzag: negative on the odd plateaus and
positive on the even ones.

\begin{code}

open plateau-path (ιₐ 0ℚ) zigzag zigzag-is-close

zigzag-path : ℝ → ℝ
zigzag-path = ψ

path-on-odd-plateau : (k : ℕ) (s : ℝ) → α (odd-index k) < s
                    → s < β (odd-index k)
                    → zigzag-path s ＝ ιₐ (ℚ- hgt (odd-index k))
path-on-odd-plateau k s l l' =
 ψ-on-plateau (odd-pred k) s (transport (λ j → α j < s) (odd-index-is-succ k) l)
                             (transport (λ j → s < β j) (odd-index-is-succ k)
                               l')
 ∙ ap zigzag (odd-index-is-succ k ⁻¹)
 ∙ ap (λ b → zigzag' b (odd-index k)) (parity-of-odd-index k)

path-on-even-plateau : (k : ℕ) (s : ℝ) → α (even-index k) < s
                     → s < β (even-index k)
                     → zigzag-path s ＝ ιₐ (hgt (even-index k))
path-on-even-plateau k s l l' =
 ψ-on-plateau (odd-index k) s l l'
 ∙ ap (λ b → zigzag' b (even-index k)) (parity-of-even-index k)

negative-is-not-nonneg : (u : ℚ) → 0ℚ < u → ¬ (0ℝ ≤ ιₐ (ℚ- u))
negative-is-not-nonneg u l k =
 ℚ<-irrefl (ℚ- u) (ιₐ-lower⁻¹ (ℚ- u) (ℚ- u) (k (ℚ- u) (neg-is-negative u l)))

positive-is-not-nonpos : (u : ℚ) → 0ℚ < u → ¬ (ιₐ u ≤ 0ℝ)
positive-is-not-nonpos u l k = ℚ<-irrefl 0ℚ (k 0ℚ (ιₐ-lower 0ℚ u l))

\end{code}

The theorem, assuming that every map ℝ → Q is constant.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 analytic-LLPO-fails : ¬ Analytic-LLPO
 analytic-LLPO-fails llpo =
  ∥∥-rec 𝟘-is-prop γ
   (finite-chain-lemma.depth-is-somewhere-₁ ν c c-is-monotone
     (ιₐ 0ℚ) (ιₐ 1ℚ) α m β α-below-m m-below-β m-decreases
     left-below-m m-below-right A D A-is-prop D-is-prop cover
     A-misses-odd-plateaus D-misses-even-plateaus)
  where
   c : ℕ → 𝟚
   c _ = ₀

   c-is-monotone : (j : ℕ) → c j ＝ ₁ → c (succ j) ＝ ₁
   c-is-monotone j e = 𝟘-elim (zero-is-not-one e)

   left-below-m : (j : ℕ) → ιₐ 0ℚ < m j
   left-below-m j = ιₐ-upper 0ℚ (m j) (m-is-positive j)

   m-below-right : (j : ℕ) → m j < ιₐ 1ℚ
   m-below-right j = ιₐ-lower (m j) 1ℚ (m-below-1 j)

   A D : ℝ → 𝓤₀ ̇
   A s = 0ℝ ≤ zigzag-path s
   D s = zigzag-path s ≤ 0ℝ

   A-is-prop : (s : ℝ) → is-prop (A s)
   A-is-prop s = ≤-is-prop 0ℝ (zigzag-path s)

   D-is-prop : (s : ℝ) → is-prop (D s)
   D-is-prop s = ≤-is-prop (zigzag-path s) 0ℝ

   cover : (s : ℝ) → A s ∨ D s
   cover s = ∥∥-functor swap (llpo (zigzag-path s))
    where
     swap : D s ∔ A s → A s ∔ D s
     swap (inl d) = inr d
     swap (inr a) = inl a

   A-misses-odd-plateaus : (k : ℕ) → c (odd-index k) ＝ ₀ → (s : ℝ) → A s
                         → α (odd-index k) < s → s < β (odd-index k) → 𝟘 {𝓤₀}
   A-misses-odd-plateaus k _ s a l l' =
    negative-is-not-nonneg (hgt (odd-index k)) (hgt-is-positive (odd-index k))
     (transport (0ℝ ≤_) (path-on-odd-plateau k s l l') a)

   D-misses-even-plateaus : (k : ℕ) → c (even-index k) ＝ ₀ → (s : ℝ) → D s
                          → α (even-index k) < s → s < β (even-index k) → 𝟘 {𝓤₀}
   D-misses-even-plateaus k _ s d l l' =
    positive-is-not-nonpos (hgt (even-index k)) (hgt-is-positive (even-index k))
     (transport (_≤ 0ℝ) (path-on-even-plateau k s l l') d)

   γ : (Σ j ꞉ ℕ , c j ＝ ₁) → 𝟘
   γ (j , e) = zero-is-not-one e

\end{code}
