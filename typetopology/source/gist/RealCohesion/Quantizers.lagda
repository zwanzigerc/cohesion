Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Staircase quantizers.

GPT-6 Astra's proof of rational detection [1, §§2–3] rounds an
arbitrary real number x without deciding anything about it. It uses
two staircases, functions ℝ → ℝ that are constant and rational on
plateaus and move linearly in between. The plateaus of one staircase
are centred at the points of a grid, those of the other at the
midpoints, and together they cover ℝ with overlaps. So at every scale
x lies, merely, on a plateau of one of the two, where its value is
rational, and both values are close to x. We never choose which of
the two is rational.

Astra glues the staircase from local formulas on an open cover of ℝ.
We use a finite sum of clamps instead, which needs no gluing. This
works because, after a translation by a rational, x lies near 1/2, so
at each scale only finitely many steps matter.

Fix a positive rational unit e and an origin o. The grid points are
base k = o + 8 e k. The k-th step is the clamp of 4 (s - base k - 3 e)
to [0 , 8 e]. It is 0 for s ≤ base k + 3 e and 8 e for
s ≥ base k + 5 e, and doubling twice makes its slope 4. The staircase
Q K s is o plus the sum of the first K steps. Measured in units of e:

 * Q K s is base (k + 1) on the plateau (base k + 5 , base k + 11);
 * Q K s lies between base (k + 1) and base (k + 2) on the extended
   cell (base k + 5 , base k + 19);
 * so on the extended cell Q K s is within 11 e of s.

The staircase with origin 0 has its plateaus at the multiples of 8 e,
and the one with origin 4 e at the midpoints. The plateaus have radius
3 e and their centres are 4 e apart, so they overlap. For a real number
with a rational approximation r to within e, a search over the grid
finds the cell of r, and three cases on the position of r in its cell
show that the real number lies on a plateau of one of the two
staircases.

We use the scale e = 2⁻⁽ʲ⁺⁶⁾ at level j. Then 11 e is less than
2⁻⁽ʲ⁺¹⁾, the modulus that sequential hitting needs.

[1] GPT-6 Astra. Positive rational detection, 10 November 2026.
    references/A11-positive-rational-detection.txt

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.Quantizers
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order hiding (max)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import UF.Subsingletons-FunExt using (Π₂-is-prop)
open import gist.RealCohesion.RationalArithmetic
 using (<-move-left ; <-move-right ; ≤-sub-right ; monotone-from-steps)
open import gist.RealCohesion.RationalArithmetic
 using (mult ; mult-zero ; mult-succ ; mult-add ; mult-nonneg ; mult-mono ;
         mult-one ;
        mult-half) public
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RealLimits fe pe pt
 using (ρ ; ρ-halves ; ρ-is-positive ; ρ-decreases ; ρ-antitone ; within ;
        within-weaken ; rational-approximations-exist)

open PropositionalTruncation pt

\end{code}

Multiples of a rational unit: mult e n ＝ n · e. The function mult and
its first facts are in gist.RealCohesion.RationalArithmetic and
re-exported above.

\begin{code}

two^ : ℕ → ℕ
two^ 0        = 1
two^ (succ n) = two^ n +ℕ two^ n

abstract
 mult-double : (n a : ℕ) → mult (ρ (succ n)) (a +ℕ a) ＝ mult (ρ n) a
 mult-double n = mult-half (ρ n)

 mult-eight : (n : ℕ) → mult (ρ (n +ℕ 3)) 8 ＝ ρ n
 mult-eight n =
  mult-double (n +ℕ 2) 4 ∙ mult-double (n +ℕ 1) 2 ∙ mult-double n 1
              ∙ mult-one (ρ n)

 mult-sixteen : (n : ℕ) → mult (ρ (n +ℕ 4)) 16 ＝ ρ n
 mult-sixteen n = mult-double (n +ℕ 3) 8 ∙ mult-eight n

 mult-two^ : (n : ℕ) → mult (ρ n) (two^ (succ n)) ＝ 1ℚ
 mult-two^ 0        =
  mult-succ (ρ 0) 1 ∙ ap (_ℚ+ ρ 0) (mult-one (ρ 0)) ∙ 1/2+1/2
 mult-two^ (succ n) = mult-double n (two^ (succ n)) ∙ mult-two^ n

le-zero : (m : ℕ) → m ≤ 0 → m ＝ 0
le-zero = zero-least''

\end{code}

The staircase with unit e and origin o.

\begin{code}

module staircase
        (e : ℚ)
        (e-is-positive : 0ℚ < e)
        (o : ℚ)
       where

 e-is-nonneg : 0ℚ ≤ e
 e-is-nonneg = ℚ<-coarser-than-≤ 0ℚ e e-is-positive

 step : ℚ
 step = mult e 8

 step-is-nonneg : 0ℚ ≤ step
 step-is-nonneg = mult-nonneg e e-is-nonneg 8

 base : ℕ → ℚ
 base 0        = o
 base (succ k) = base k ℚ+ step

 base-increases : (k : ℕ) → base k ≤ base (succ k)
 base-increases k = transport (_≤ base (succ k)) (ℚ-zero-right-neutral (base k))
                     (ℚ≤-adding (base k) (base k) 0ℚ step (ℚ≤-refl (base k))
                       step-is-nonneg)

 base-mono : (m k : ℕ) → m ≤ k → base m ≤ base k
 base-mono =
  monotone-from-steps (λ u v → u ≤ v) ℚ≤-refl ℚ≤-trans base base-increases

 add-left : (c : ℚ) (a b : ℕ) → a ≤ b → c ℚ+ mult e a ≤ c ℚ+ mult e b
 add-left c a b l = ℚ≤-adding c c (mult e a) (mult e b) (ℚ≤-refl c)
                     (mult-mono e e-is-nonneg a b l)

 term : ℕ → ℝ → ℝ
 term m s =
  clamp (ιₐ 0ℚ) (ιₐ step) (double (double (s + ιₐ (ℚ- (base m ℚ+ mult e 3)))))

 Q : ℕ → ℝ → ℝ
 Q 0        s = ιₐ o
 Q (succ K) s = Q K s + term K s

\end{code}

The steps: saturated above base m + 5 e, zero below base m + 3 e,
and always between 0 and 8 e.

\begin{code}

 double-ιₐ : (c : ℚ) → double (ιₐ c) ＝ ιₐ (c ℚ+ c)
 double-ιₐ c = ιₐ-sum c c

 term-top : (m : ℕ) (s : ℝ) → (base m ℚ+ mult e 5) < s → term m s ＝ ιₐ step
 term-top m s l =
  clamp-above (ιₐ 0ℚ) (ιₐ step) t (ιₐ-≤-ιₐ 0ℚ step step-is-nonneg) II
  where
   t : ℝ
   t = double (double (s + ιₐ (ℚ- (base m ℚ+ mult e 3))))

   identity : mult e 2 ℚ+ (base m ℚ+ mult e 3) ＝ base m ℚ+ mult e 5
   identity = ℚ+-assoc (mult e 2) (base m) (mult e 3) ⁻¹
            ∙ ap (_ℚ+ mult e 3) (ℚ+-comm (mult e 2) (base m))
            ∙ ℚ+-assoc (base m) (mult e 2) (mult e 3)
            ∙ ap (base m ℚ+_) (mult-add e 2 3 ⁻¹)

   I : ιₐ (mult e 2) ≤ s + ιₐ (ℚ- (base m ℚ+ mult e 3))
   I = translate-above s (mult e 2) (base m ℚ+ mult e 3)
        (transport (_< s) (identity ⁻¹) l)

   eight : double (double (ιₐ (mult e 2))) ＝ ιₐ step
   eight = ap double (double-ιₐ (mult e 2) ∙ ap ιₐ (mult-add e 2 2 ⁻¹))
         ∙ double-ιₐ (mult e 4) ∙ ap ιₐ (mult-add e 4 4 ⁻¹)

   II : ιₐ step ≤ t
   II = transport (_≤ t) eight
         (≤-double (double (ιₐ (mult e 2)))
           (double (s + ιₐ (ℚ- (base m ℚ+ mult e 3))))
           (≤-double (ιₐ (mult e 2)) (s + ιₐ (ℚ- (base m ℚ+ mult e 3))) I))

 term-bottom : (m : ℕ) (s : ℝ) → s < (base m ℚ+ mult e 3) → term m s ＝ ιₐ 0ℚ
 term-bottom m s l = clamp-below (ιₐ 0ℚ) (ιₐ step) t II
  where
   t : ℝ
   t = double (double (s + ιₐ (ℚ- (base m ℚ+ mult e 3))))

   I : s + ιₐ (ℚ- (base m ℚ+ mult e 3)) ≤ ιₐ 0ℚ
   I = translate-below s 0ℚ (base m ℚ+ mult e 3)
        (transport (s <_) (ℚ-zero-left-neutral (base m ℚ+ mult e 3) ⁻¹) l)

   zeros : double (double (ιₐ 0ℚ)) ＝ ιₐ 0ℚ
   zeros = ap double (double-ιₐ 0ℚ ∙ ap ιₐ (ℚ-zero-left-neutral 0ℚ))
         ∙ double-ιₐ 0ℚ ∙ ap ιₐ (ℚ-zero-left-neutral 0ℚ)

   II : t ≤ ιₐ 0ℚ
   II = transport (t ≤_) zeros
         (≤-double (double (s + ιₐ (ℚ- (base m ℚ+ mult e 3)))) (double (ιₐ 0ℚ))
           (≤-double (s + ιₐ (ℚ- (base m ℚ+ mult e 3))) (ιₐ 0ℚ) I))

 term-bounds : (m : ℕ) (s : ℝ) → (ιₐ 0ℚ ≤ term m s) × (term m s ≤ ιₐ step)
 term-bounds m s = clamp-is-above-lo (ιₐ 0ℚ) (ιₐ step) t ,
                   clamp-is-below-hi (ιₐ 0ℚ) (ιₐ step) t
                    (ιₐ-≤-ιₐ 0ℚ step step-is-nonneg)
  where
   t : ℝ
   t = double (double (s + ιₐ (ℚ- (base m ℚ+ mult e 3))))

\end{code}

The staircase on plateaus and on extended cells.

\begin{code}

 Q-saturated : (K : ℕ) (s : ℝ)
             → ((m : ℕ) → m < K → (base m ℚ+ mult e 5) < s)
             → Q K s ＝ ιₐ (base K)
 Q-saturated 0        s h = refl
 Q-saturated (succ K) s h =
  ap₂ _+_ (Q-saturated K s (λ m l → h m (<-trans m K (succ K) l (<-succ K))))
          (term-top K s (h K (<-succ K)))
  ∙ ιₐ-sum (base K) step

 Q-frozen : (k K : ℕ) (s : ℝ) → k ≤ K
          → ((m : ℕ) → k ≤ m → s < (base m ℚ+ mult e 3))
          → Q K s ＝ Q k s
 Q-frozen k 0        s l h = ap (λ - → Q - s) (le-zero k l ⁻¹)
 Q-frozen k (succ K) s l h = Cases (≤-split k K l) γ δ
  where
   γ : k ≤ K → Q (succ K) s ＝ Q k s
   γ l' = ap (Q K s +_) (term-bottom K s (h K l')) ∙ plus-zero (Q K s)
          ∙ Q-frozen k K s l' h

   δ : k ＝ succ K → Q (succ K) s ＝ Q k s
   δ p = ap (λ - → Q - s) (p ⁻¹)

 saturated-below : (k : ℕ) (s : ℝ) → (base k ℚ+ mult e 5) < s
                 → (m : ℕ) → m < succ k → (base m ℚ+ mult e 5) < s
 saturated-below k s a m l =
  use-rounded-real-L' s (base m ℚ+ mult e 5) (base k ℚ+ mult e 5)
                              (ℚ≤-addition-preserves-order (base m) (base k)
                                (mult e 5)
                                (base-mono m k l))
                              a

 frozen-above : (k : ℕ) (s : ℝ) → s < (base k ℚ+ mult e 3)
              → (m : ℕ) → k ≤ m → s < (base m ℚ+ mult e 3)
 frozen-above k s b m l =
  use-rounded-real-R' s (base k ℚ+ mult e 3) (base m ℚ+ mult e 3)
                           (ℚ≤-addition-preserves-order (base k) (base m)
                             (mult e 3)
                             (base-mono k m l))
                           b

 Q-plateau : (k K : ℕ) (s : ℝ) → succ k ≤ K
           → (base k ℚ+ mult e 5) < s → s < (base (succ k) ℚ+ mult e 3)
           → Q K s ＝ ιₐ (base (succ k))
 Q-plateau k K s l a b = Q-frozen (succ k) K s l (frozen-above (succ k) s b)
                       ∙ Q-saturated (succ k) s (saturated-below k s a)

 Q-extended : (k K : ℕ) (s : ℝ) → succ (succ k) ≤ K
            → (base k ℚ+ mult e 5) < s → s < (base (succ (succ k)) ℚ+ mult e 3)
            → (ιₐ (base (succ k)) ≤ Q K s) × (Q K s ≤ ιₐ (base (succ (succ k))))
 Q-extended k K s l a b = transport (λ - → (ιₐ (base (succ k)) ≤ -)
                                         × (- ≤ ιₐ (base (succ (succ k)))))
                           (p ⁻¹) (I , II)
  where
   p : Q K s ＝ ιₐ (base (succ k)) + term (succ k) s
   p = Q-frozen (succ (succ k)) K s l (frozen-above (succ (succ k)) s b)
     ∙ ap (_+ term (succ k) s) (Q-saturated (succ k) s (saturated-below k s a))

   I : ιₐ (base (succ k)) ≤ ιₐ (base (succ k)) + term (succ k) s
   I = transport (_≤ ιₐ (base (succ k)) + term (succ k) s)
        (plus-zero (ιₐ (base (succ k))))
        (sum-≤ (ιₐ (base (succ k))) (ιₐ (base (succ k))) (ιₐ 0ℚ)
          (term (succ k) s)
          (λ _ m → m) (pr₁ (term-bounds (succ k) s)))

   II : ιₐ (base (succ k)) + term (succ k) s ≤ ιₐ (base (succ (succ k)))
   II = transport (ιₐ (base (succ k)) + term (succ k) s ≤_)
         (ιₐ-sum (base (succ k)) step)
         (sum-≤ (ιₐ (base (succ k))) (ιₐ (base (succ k))) (term (succ k) s)
           (ιₐ step)
           (λ _ m → m) (pr₂ (term-bounds (succ k) s)))

 Q-close : (k K : ℕ) (s : ℝ) → succ (succ k) ≤ K
         → (base k ℚ+ mult e 5) < s → s < (base (succ (succ k)) ℚ+ mult e 3)
         → within (mult e 11) (Q K s) s
 Q-close k K s l a b = I , II
  where
   bounds : (ιₐ (base (succ k)) ≤ Q K s) × (Q K s ≤ ιₐ (base (succ (succ k))))
   bounds = Q-extended k K s l a b

   i₁ : (base k ℚ+ mult e 5) ℚ+ mult e 11 ＝ base (succ (succ k))
   i₁ = ℚ+-assoc (base k) (mult e 5) (mult e 11)
      ∙ ap (base k ℚ+_) (mult-add e 5 11 ⁻¹ ∙ mult-add e 8 8)
      ∙ ℚ+-assoc (base k) step step ⁻¹

   i₂ : base (succ k) ℚ+ mult e 11 ＝ base (succ (succ k)) ℚ+ mult e 3
   i₂ = ap (base (succ k) ℚ+_) (mult-add e 8 3)
        ∙ ℚ+-assoc (base (succ k)) step (mult e 3) ⁻¹

   I : (p : ℚ) → p < Q K s → (p ℚ- mult e 11) < s
   I p o = use-rounded-real-L s (p ℚ- mult e 11) (base k ℚ+ mult e 5)
            (<-move-left p (base k ℚ+ mult e 5) (mult e 11)
              (transport (p <_) (i₁ ⁻¹)
                (ιₐ-lower⁻¹ p (base (succ (succ k))) (pr₂ bounds p o))))
            a

   II : (p : ℚ) → p < s → (p ℚ- mult e 11) < Q K s
   II p o = pr₁ bounds (p ℚ- mult e 11)
             (ιₐ-lower (p ℚ- mult e 11) (base (succ k))
               (<-move-left p (base (succ k)) (mult e 11)
                 (transport (p <_) (i₂ ⁻¹)
                   (cuts-are-ordered s p (base (succ (succ k)) ℚ+ mult e 3) o
                     b))))

\end{code}

The cell of a rational number in the grid.

\begin{code}

 cell-search : (K : ℕ) (r : ℚ) → base 1 ≤ r → r < base K
             → Σ k ꞉ ℕ , (base (succ k) ≤ r) × (r < base (succ (succ k)))
                       × (succ (succ k) ≤ K)
 cell-search 0        r l m = 𝟘-elim (ℚ<-irrefl r (ℚ<-≤-trans r (base 0) r m
                                (ℚ≤-trans (base 0) (base 1) r (base-increases 0)
                                  l)))
 cell-search (succ K) r l m = γ (ℚ-dichotomous' r (base K))
  where
   δ : (K' : ℕ) → base K' ≤ r → r < base (succ K')
     → Σ k ꞉ ℕ , (base (succ k) ≤ r) × (r < base (succ (succ k)))
               × (succ (succ k) ≤ succ K')
   δ 0         l' m' = 𝟘-elim (ℚ<-irrefl r (ℚ<-≤-trans r (base 1) r m' l))
   δ (succ k)  l' m' = k , l' , m' , ≤-refl (succ (succ k))

   γ : (r < base K) ∔ (base K ≤ r)
     → Σ k ꞉ ℕ , (base (succ k) ≤ r) × (r < base (succ (succ k)))
               × (succ (succ k) ≤ succ K)
   γ (inl m') = k , pr₁ σ , pr₁ (pr₂ σ) ,
                ≤-trans (succ (succ k)) K (succ K) (pr₂ (pr₂ σ)) (≤-succ K)
    where
     σ' = cell-search K r l m'
     k  = pr₁ σ'
     σ  = pr₂ σ'
   γ (inr l') = δ K l' m

\end{code}

Closeness, from a rational approximation to within e.

\begin{code}

 Q-close' : (K : ℕ) (s : ℝ) (r : ℚ)
          → (r ℚ- e) < s → s < (r ℚ+ e)
          → base 1 ≤ r → r < base K
          → within (mult e 11) (Q K s) s
 Q-close' K s r a b l m = Q-close k K s (pr₂ (pr₂ σ)) lower upper
  where
   σ' = cell-search K r l m
   k  = pr₁ σ'
   σ  = pr₂ σ'

   lower : (base k ℚ+ mult e 5) < s
   lower = use-rounded-real-L' s (base k ℚ+ mult e 5) (r ℚ- e)
            (≤-sub-right (base k ℚ+ mult e 5) r e
              (transport (_≤ r) ((ℚ+-assoc (base k) (mult e 5) e
                                  ∙ ap (base k ℚ+_) (mult-succ e 5 ⁻¹)) ⁻¹)
                (ℚ≤-trans (base k ℚ+ mult e 6) (base (succ k)) r
                  (add-left (base k) 6 8 ⋆) (pr₁ σ))))
            a

   upper : s < (base (succ (succ k)) ℚ+ mult e 3)
   upper = use-rounded-real-R s (r ℚ+ e) (base (succ (succ k)) ℚ+ mult e 3)
            (ℚ<-≤-trans (r ℚ+ e) (base (succ (succ k)) ℚ+ e)
              (base (succ (succ k)) ℚ+ mult e 3)
              (ℚ<-addition-preserves-order r (base (succ (succ k))) e
                (pr₁ (pr₂ σ)))
              (transport (λ - →
                base (succ (succ k)) ℚ+ - ≤ base (succ (succ k)) ℚ+ mult e 3)
                (mult-one e) (add-left (base (succ (succ k))) 1 3 ⋆)))
            b

\end{code}

The pair of staircases, with origins 0 and 4 e. A real number with a
rational approximation to within e lies on a plateau of one of them.

\begin{code}

module quantizer-pair
        (e : ℚ)
        (e-is-positive : 0ℚ < e)
       where

 module S₀ = staircase e e-is-positive 0ℚ
 module S₄ = staircase e e-is-positive (mult e 4)

 base-shift : (k : ℕ) → S₄.base k ＝ S₀.base k ℚ+ mult e 4
 base-shift 0        = ℚ-zero-left-neutral (mult e 4) ⁻¹
 base-shift (succ k) = ap (_ℚ+ mult e 8) (base-shift k)
                     ∙ ℚ+-assoc (S₀.base k) (mult e 4) (mult e 8)
                     ∙ ap (S₀.base k ℚ+_) (ℚ+-comm (mult e 4) (mult e 8))
                     ∙ ℚ+-assoc (S₀.base k) (mult e 8) (mult e 4) ⁻¹

 plus-e : (c : ℚ) (i : ℕ) → (c ℚ+ mult e i) ℚ+ e ＝ c ℚ+ mult e (succ i)
 plus-e c i = ℚ+-assoc c (mult e i) e ∙ ap (c ℚ+_) (mult-succ e i ⁻¹)

 cover : (K : ℕ) (s : ℝ) (r : ℚ)
       → (r ℚ- e) < s → s < (r ℚ+ e)
       → S₀.base 1 ≤ r → r < S₀.base K
       → (Σ q ꞉ ℚ , S₀.Q K s ＝ ιₐ q) ∔ (Σ q ꞉ ℚ , S₄.Q K s ＝ ιₐ q)
 cover K s r a b l m = γ (S₀.cell-search K r l m)
  where
   Goal : 𝓤₁ ̇
   Goal = (Σ q ꞉ ℚ , S₀.Q K s ＝ ιₐ q) ∔ (Σ q ꞉ ℚ , S₄.Q K s ＝ ιₐ q)

   below : (c : ℚ) → c ℚ+ e ≤ r → c < s
   below c l' = use-rounded-real-L' s c (r ℚ- e) (≤-sub-right c r e l') a

   above : (c : ℚ) → r ℚ+ e < c → s < c
   above c l' = use-rounded-real-R s (r ℚ+ e) c l' b

   γ : (Σ k ꞉ ℕ , (S₀.base (succ k) ≤ r) × (r < S₀.base (succ (succ k)))
                × (succ (succ k) ≤ K))
     → Goal
   γ (k , c , d , n) = δ (ℚ-dichotomous' r (S₀.base (succ k) ℚ+ mult e 2))
    where
     n' : succ k ≤ K
     n' = ≤-trans (succ k) (succ (succ k)) K (≤-succ (succ k)) n

     δ : (r < S₀.base (succ k) ℚ+ mult e 2) ∔ (S₀.base (succ k) ℚ+ mult e 2 ≤ r)
       → Goal
     δ (inl o) = inl (S₀.base (succ k) , S₀.Q-plateau k K s n' lower upper)
      where
       lower : (S₀.base k ℚ+ mult e 5) < s
       lower = below (S₀.base k ℚ+ mult e 5)
                (transport (_≤ r) (plus-e (S₀.base k) 5 ⁻¹)
                  (ℚ≤-trans (S₀.base k ℚ+ mult e 6) (S₀.base (succ k)) r
                    (S₀.add-left (S₀.base k) 6 8 ⋆) c))

       upper : s < (S₀.base (succ k) ℚ+ mult e 3)
       upper = above (S₀.base (succ k) ℚ+ mult e 3)
                (transport (r ℚ+ e <_) (plus-e (S₀.base (succ k)) 2)
                  (ℚ<-addition-preserves-order r (S₀.base (succ k) ℚ+ mult e 2)
                    e o))
     δ (inr o) = ε (ℚ-dichotomous' r (S₀.base (succ k) ℚ+ mult e 6))
      where
       ε : (r < S₀.base (succ k) ℚ+ mult e 6)
         ∔ (S₀.base (succ k) ℚ+ mult e 6 ≤ r) → Goal
       ε (inl o') = inr (S₄.base (succ k) , S₄.Q-plateau k K s n' lower upper)
        where
         i₁ : (S₄.base k ℚ+ mult e 5) ℚ+ e ＝ S₀.base (succ k) ℚ+ mult e 2
         i₁ = plus-e (S₄.base k) 5
            ∙ ap (_ℚ+ mult e 6) (base-shift k)
            ∙ ℚ+-assoc (S₀.base k) (mult e 4) (mult e 6)
            ∙ ap (S₀.base k ℚ+_) (mult-add e 4 6 ⁻¹ ∙ mult-add e 8 2)
            ∙ ℚ+-assoc (S₀.base k) (mult e 8) (mult e 2) ⁻¹

         lower : (S₄.base k ℚ+ mult e 5) < s
         lower = below (S₄.base k ℚ+ mult e 5) (transport (_≤ r) (i₁ ⁻¹) o)

         i₂ : S₀.base (succ k) ℚ+ mult e 7 ＝ S₄.base (succ k) ℚ+ mult e 3
         i₂ = ap (S₀.base (succ k) ℚ+_) (mult-add e 4 3)
            ∙ ℚ+-assoc (S₀.base (succ k)) (mult e 4) (mult e 3) ⁻¹
            ∙ ap (_ℚ+ mult e 3) (base-shift (succ k) ⁻¹)

         upper : s < (S₄.base (succ k) ℚ+ mult e 3)
         upper = above (S₄.base (succ k) ℚ+ mult e 3)
                  (transport (r ℚ+ e <_) (plus-e (S₀.base (succ k)) 6 ∙ i₂)
                    (ℚ<-addition-preserves-order r
                      (S₀.base (succ k) ℚ+ mult e 6) e o'))
       ε (inr o') =
        inl (S₀.base (succ (succ k)) , S₀.Q-plateau (succ k) K s n lower upper)
        where
         lower : (S₀.base (succ k) ℚ+ mult e 5) < s
         lower = below (S₀.base (succ k) ℚ+ mult e 5)
                  (transport (_≤ r) (plus-e (S₀.base (succ k)) 5 ⁻¹) o')

         upper : s < (S₀.base (succ (succ k)) ℚ+ mult e 3)
         upper = above (S₀.base (succ (succ k)) ℚ+ mult e 3)
                  (ℚ<-≤-trans (r ℚ+ e) (S₀.base (succ (succ k)) ℚ+ e)
                    (S₀.base (succ (succ k)) ℚ+ mult e 3)
                    (ℚ<-addition-preserves-order r (S₀.base (succ (succ k))) e
                      d)
                    (transport (λ - → S₀.base (succ (succ k)) ℚ+ -
                                     ≤ S₀.base (succ (succ k)) ℚ+ mult e 3)
                      (mult-one e)
                       (S₀.add-left (S₀.base (succ (succ k))) 1 3 ⋆)))

\end{code}

The two quantizers at level j, with unit e = ρ (j + 5) = 2⁻⁽ʲ⁺⁶⁾ and
2ʲ⁺³ steps, applied to a real number between 1/2 and 1/2 + ρ 4.

\begin{code}

within-is-prop : (ε : ℚ) (x y : ℝ) → is-prop (within ε x y)
within-is-prop ε x y = ×-is-prop
                        (Π₂-is-prop fe (λ p _ → ℚ<ℝ-is-prop (p ℚ- ε) y))
                        (Π₂-is-prop fe (λ p _ → ℚ<ℝ-is-prop (p ℚ- ε) x))

module level (j : ℕ) where

 e : ℚ
 e = ρ (j +ℕ 5)

 e-is-positive : 0ℚ < e
 e-is-positive = ρ-is-positive (j +ℕ 5)

 open quantizer-pair e e-is-positive

 K : ℕ
 K = two^ (j +ℕ 3)

 Q⁰ Q¹ : ℝ → ℝ
 Q⁰ = S₀.Q K
 Q¹ = S₄.Q K

 base₀-is-mult : (k : ℕ) → S₀.base k ＝ mult (mult e 8) k
 base₀-is-mult 0        = mult-zero (mult e 8) ⁻¹
 base₀-is-mult (succ k) =
  ap (_ℚ+ mult e 8) (base₀-is-mult k) ∙ mult-succ (mult e 8) k ⁻¹

 e-eight : mult e 8 ＝ ρ (j +ℕ 2)
 e-eight = transport (λ n → mult (ρ n) 8 ＝ ρ (j +ℕ 2)) p (mult-eight (j +ℕ 2))
  where
   p : (j +ℕ 2) +ℕ 3 ＝ j +ℕ 5
   p = refl

 e-sixteen : mult e 16 ＝ ρ (succ j)
 e-sixteen =
  transport (λ n → mult (ρ n) 16 ＝ ρ (succ j)) p (mult-sixteen (succ j))
  where
   p : succ j +ℕ 4 ＝ j +ℕ 5
   p = refl

 base₀-at-K : S₀.base K ＝ 1ℚ
 base₀-at-K = base₀-is-mult K
            ∙ ap (λ - → mult - K) e-eight
            ∙ mult-two^ (j +ℕ 2)

 base₀-below-base₄ : (k : ℕ) → S₀.base k ≤ S₄.base k
 base₀-below-base₄ k =
  transport (_≤ S₄.base k) (ℚ-zero-right-neutral (S₀.base k))
                        (transport (S₀.base k ℚ+ 0ℚ ≤_) (base-shift k ⁻¹)
                          (ℚ≤-adding (S₀.base k) (S₀.base k) 0ℚ (mult e 4)
                            (ℚ≤-refl (S₀.base k))
                            (mult-nonneg e
                              (ℚ<-coarser-than-≤ 0ℚ e e-is-positive) 4)))

 eleven-below-ρ : mult e 11 ≤ ρ j
 eleven-below-ρ = ℚ≤-trans (mult e 11) (mult e 16) (ρ j)
                   (mult-mono e (ℚ<-coarser-than-≤ 0ℚ e e-is-positive) 11 16 ⋆)
                   (transport (_≤ ρ j) (e-sixteen ⁻¹)
                     (ℚ<-coarser-than-≤ (ρ (succ j)) (ρ j) (ρ-decreases j)))

 approximation : (x : ℝ) → ∃ r ꞉ ℚ , ((r ℚ- e) < x) × (x < (r ℚ+ e))
 approximation x = rational-approximations-exist x e e-is-positive

\end{code}

The range of the rational approximation of a real number between 1/2
and 1/2 + ρ 4.

\begin{code}

 module _ (x : ℝ) (x-above : 1/2 < x) (x-below : x < 1/2 ℚ+ ρ 4)
          (r : ℚ) (a : (r ℚ- e) < x) (b : x < (r ℚ+ e))
        where

  base₄-at-1-below : S₄.base 1 ≤ r
  base₄-at-1-below = ℚ<-coarser-than-≤ (S₄.base 1) r
                      (ℚ<-cancel-left e (S₄.base 1) r
                        (transport₂ _<_ (ℚ+-comm (S₄.base 1) e) (ℚ+-comm r e)
                          III))
   where
    I : S₄.base 1 ℚ+ e ＝ mult e 13
    I = ap (_ℚ+ e) (mult-add e 4 8 ⁻¹) ∙ mult-succ e 12 ⁻¹

    II : mult e 13 ≤ 1/2
    II = ℚ≤-trans (mult e 13) (mult e 16) 1/2
          (mult-mono e (ℚ<-coarser-than-≤ 0ℚ e e-is-positive) 13 16 ⋆)
          (transport (_≤ 1/2) (e-sixteen ⁻¹) (ρ-antitone 0 (succ j) ⋆))

    III : S₄.base 1 ℚ+ e < r ℚ+ e
    III = ℚ≤-<-trans (S₄.base 1 ℚ+ e) 1/2 (r ℚ+ e)
           (transport (_≤ 1/2) (I ⁻¹) II)
           (cuts-are-ordered x 1/2 (r ℚ+ e) x-above b)

  base₀-at-1-below : S₀.base 1 ≤ r
  base₀-at-1-below =
   ℚ≤-trans (S₀.base 1) (S₄.base 1) r (base₀-below-base₄ 1) base₄-at-1-below

  below-base₀-at-K : r < S₀.base K
  below-base₀-at-K = transport (r <_) (base₀-at-K ⁻¹)
                      (ℚ<-≤-trans r ((1/2 ℚ+ ρ 4) ℚ+ e) 1ℚ I II)
   where
    I : r < (1/2 ℚ+ ρ 4) ℚ+ e
    I = <-move-right r (1/2 ℚ+ ρ 4) e
         (cuts-are-ordered x (r ℚ- e) (1/2 ℚ+ ρ 4) a x-below)

    II : (1/2 ℚ+ ρ 4) ℚ+ e ≤ 1ℚ
    II = ℚ≤-trans ((1/2 ℚ+ ρ 4) ℚ+ e) (1/2 ℚ+ (ρ 4 ℚ+ ρ 4)) 1ℚ
          (transport (_≤ 1/2 ℚ+ (ρ 4 ℚ+ ρ 4)) (ℚ+-assoc 1/2 (ρ 4) e ⁻¹)
            (ℚ≤-adding 1/2 1/2 (ρ 4 ℚ+ e) (ρ 4 ℚ+ ρ 4) (ℚ≤-refl 1/2)
              (ℚ≤-adding (ρ 4) (ρ 4) e (ρ 4) (ℚ≤-refl (ρ 4))
                (ρ-antitone 4 (j +ℕ 5) (≤-+' j 5)))))
          (transport (λ - → 1/2 ℚ+ - ≤ 1ℚ) (ρ-halves 3 ⁻¹)
            (transport (1/2 ℚ+ ρ 3 ≤_) 1/2+1/2
              (ℚ≤-adding 1/2 1/2 (ρ 3) 1/2 (ℚ≤-refl 1/2) (ρ-antitone 0 3 ⋆))))

  below-base₄-at-K : r < S₄.base K
  below-base₄-at-K =
   ℚ<-≤-trans r (S₀.base K) (S₄.base K) below-base₀-at-K (base₀-below-base₄ K)

\end{code}

The quantizers are close to x, and one of them is rational at x.

\begin{code}

 Q⁰-close : (x : ℝ) → 1/2 < x → x < 1/2 ℚ+ ρ 4 → within (ρ j) (Q⁰ x) x
 Q⁰-close x l m = ∥∥-rec (within-is-prop (ρ j) (Q⁰ x) x) γ (approximation x)
  where
   γ : (Σ r ꞉ ℚ , ((r ℚ- e) < x) × (x < (r ℚ+ e))) → within (ρ j) (Q⁰ x) x
   γ (r , a , b) = within-weaken (mult e 11) (ρ j) (Q⁰ x) x eleven-below-ρ
                    (S₀.Q-close' K x r a b (base₀-at-1-below x l m r a b)
                      (below-base₀-at-K x l m r a b))

 Q¹-close : (x : ℝ) → 1/2 < x → x < 1/2 ℚ+ ρ 4 → within (ρ j) (Q¹ x) x
 Q¹-close x l m = ∥∥-rec (within-is-prop (ρ j) (Q¹ x) x) γ (approximation x)
  where
   γ : (Σ r ꞉ ℚ , ((r ℚ- e) < x) × (x < (r ℚ+ e))) → within (ρ j) (Q¹ x) x
   γ (r , a , b) = within-weaken (mult e 11) (ρ j) (Q¹ x) x eleven-below-ρ
                    (S₄.Q-close' K x r a b (base₄-at-1-below x l m r a b)
                      (below-base₄-at-K x l m r a b))

 Q-is-rational : (x : ℝ) → 1/2 < x → x < 1/2 ℚ+ ρ 4
               → ∥ (Σ q ꞉ ℚ , Q⁰ x ＝ ιₐ q) ∔ (Σ q ꞉ ℚ , Q¹ x ＝ ιₐ q) ∥
 Q-is-rational x l m = ∥∥-functor γ (approximation x)
  where
   γ : (Σ r ꞉ ℚ , ((r ℚ- e) < x) × (x < (r ℚ+ e)))
     → (Σ q ꞉ ℚ , Q⁰ x ＝ ιₐ q) ∔ (Σ q ꞉ ℚ , Q¹ x ＝ ιₐ q)
   γ (r , a , b) = cover K x r a b (base₀-at-1-below x l m r a b)
                    (below-base₀-at-K x l m r a b)

\end{code}
