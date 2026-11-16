Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The reduction of the approximate intermediate value theorem to its
normal form (Part V of the formalization blueprint [1]).

Let f : ℝ → ℝ and p q a b : ℝ with p < q, f a < q and p < f b, none
of them crisp. If every map ℝ → Q is constant, then p < f x < q for
some x. Choose rationals p < r < s < q. By cotransitivity, p < f a, in
which case x := a works, or f a < r; and f b < q, in which case
x := b works, or s < f b. In the remaining case put

  φ x := a moved towards b by at most 2ᵏ x, exactly b at x = 1,
  g x := 2ⁿ⁺¹ (f (φ x) - r),

where 2ᵏ bounds |b - a| and 2⁻⁽ⁿ⁺¹⁾ < s - r. Then g 0 < 0 ≤ 1/3,
g 1 > 1 ≥ 2/3, and 0 < g x < 1 gives r < f (φ x) < s. The normal form
(gist.RealCohesion.SoftBisection) gives such an x.

The path φ is a clamped step from a towards b
(gist.RealCohesion.RealLimits), whose bounds ± 2ᵏ x are themselves
clamps, so that φ 0 ＝ a and φ 1 ＝ b exactly. Multiplication by powers
of 2 is repeated doubling. The only arithmetic fact about rationals
not proved elsewhere in this folder is that the powers of 2 are
unbounded, which we derive from ρ n → 0 and the multiplicative inverse
of TypeTopology's rationals. No order between a and b is used.

[1] Formalization blueprint: the approximate IVT from Axiom R♭.
    Claude Fable 5.2, revision 3, 10 November 2026.
    references/F15-aivt-blueprint-rev3.md
    references/F16-aivt-handoff-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.ApproximateIVTReduction
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.MinMax renaming (max to ℚ-max ; min to ℚ-min)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (cuts-are-ordered)
open import gist.RealCohesion.RealLattice fe pe pt
open import gist.RealCohesion.RationalArithmetic using (neg-is-negative)
open import gist.RealCohesion.RealLimits fe pe pt
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.SoftBisection fe pe pt using (normal-form)

open PropositionalTruncation pt

\end{code}

Repeated doubling of rationals, and the powers of 2.

\begin{code}

dbl^ : ℕ → ℚ → ℚ
dbl^ 0        c = c
dbl^ (succ k) c = dbl^ k (c ℚ+ c)

dbl^-is-monotone : (k : ℕ) (c c' : ℚ) → c < c' → dbl^ k c < dbl^ k c'
dbl^-is-monotone 0        c c' l = l
dbl^-is-monotone (succ k) c c' l = dbl^-is-monotone k (c ℚ+ c) (c' ℚ+ c')
                                    (ℚ<-adding c c' c c' l l)

dbl^-of-zero : (k : ℕ) → dbl^ k 0ℚ ＝ 0ℚ
dbl^-of-zero 0        = refl
dbl^-of-zero (succ k) = ap (dbl^ k) (ℚ-zero-left-neutral 0ℚ) ∙ dbl^-of-zero k

dbl^-of-ρ : (n : ℕ) → dbl^ (succ n) (ρ n) ＝ 1ℚ
dbl^-of-ρ 0        = 1/2+1/2
dbl^-of-ρ (succ n) = ap (dbl^ (succ n)) (ρ-halves n) ∙ dbl^-of-ρ n

dbl^-is-homogeneous : (k : ℕ) (c K : ℚ) → dbl^ k (c ℚ* K) ＝ (dbl^ k c) ℚ* K
dbl^-is-homogeneous 0        c K = refl
dbl^-is-homogeneous (succ k) c K = ap (dbl^ k) (ℚ-distributivity' K c c ⁻¹)
                                   ∙ dbl^-is-homogeneous k (c ℚ+ c) K

powers-of-two-are-unbounded : (K : ℚ) → Σ k ꞉ ℕ , K < dbl^ k 1ℚ
powers-of-two-are-unbounded K = γ (ℚ-dichotomous' 0ℚ K)
 where
  γ : (0ℚ < K) ∔ (K ≤ 0ℚ) → Σ k ꞉ ℕ , K < dbl^ k 1ℚ
  γ (inr l) = 0 , ℚ≤-<-trans K 0ℚ 1ℚ l 0<1
  γ (inl l) = succ n , transport (_< dbl^ (succ n) 1ℚ) I II
   where
    nz : ¬ (K ＝ 0ℚ)
    nz e = ℚ<-irrefl 0ℚ (transport (0ℚ <_) e l)

    ε : ℚ
    ε = ℚ*-inv K nz

    small : Σ n ꞉ ℕ , ρ n < ε
    small = ρ-becomes-small ε (ℚ-inv-preserves-pos K l nz)

    n : ℕ
    n = pr₁ small

    I : dbl^ (succ n) (ρ n ℚ* K) ＝ K
    I = dbl^-is-homogeneous (succ n) (ρ n) K
      ∙ ap (_ℚ* K) (dbl^-of-ρ n)
      ∙ ℚ-mult-left-id K

    II : dbl^ (succ n) (ρ n ℚ* K) < dbl^ (succ n) 1ℚ
    II = dbl^-is-monotone (succ n) (ρ n ℚ* K) 1ℚ
          (transport (ρ n ℚ* K <_) (ℚ*-comm ε K ∙ ℚ*-inverse-product K nz)
            (ℚ<-pos-multiplication-preserves-order' (ρ n) ε K (pr₂ small) l))

\end{code}

Repeated doubling of reals.

\begin{code}

dbl-ℝ : ℕ → ℝ → ℝ
dbl-ℝ 0        x = x
dbl-ℝ (succ k) x = dbl-ℝ k (double x)

dbl-ℝ-of-ιₐ : (k : ℕ) (c : ℚ) → dbl-ℝ k (ιₐ c) ＝ ιₐ (dbl^ k c)
dbl-ℝ-of-ιₐ 0        c = refl
dbl-ℝ-of-ιₐ (succ k) c = ap (dbl-ℝ k) (ιₐ-sum c c) ∙ dbl-ℝ-of-ιₐ k (c ℚ+ c)

dbl-ℝ-≤ : (k : ℕ) (x y : ℝ) → x ≤ y → dbl-ℝ k x ≤ dbl-ℝ k y
dbl-ℝ-≤ 0        x y l = l
dbl-ℝ-≤ (succ k) x y l = dbl-ℝ-≤ k (double x) (double y) (≤-double x y l)

below-dbl-ℝ : (k : ℕ) (x : ℝ) (c : ℚ) → c < x → dbl^ k c < dbl-ℝ k x
below-dbl-ℝ 0        x c l = l
below-dbl-ℝ (succ k) x c l =
 below-dbl-ℝ k (double x) (c ℚ+ c) (below-double x c l)

below-dbl-ℝ⁻¹ : (k : ℕ) (x : ℝ) (c : ℚ) → dbl^ k c < dbl-ℝ k x → c < x
below-dbl-ℝ⁻¹ 0        x c l = l
below-dbl-ℝ⁻¹ (succ k) x c l =
 below-double⁻¹ x c (below-dbl-ℝ⁻¹ k (double x) (c ℚ+ c) l)

dbl-ℝ-below⁻¹ : (k : ℕ) (x : ℝ) (c : ℚ) → dbl-ℝ k x < dbl^ k c → x < c
dbl-ℝ-below⁻¹ 0        x c l = l
dbl-ℝ-below⁻¹ (succ k) x c l =
 double-below⁻¹ x c (dbl-ℝ-below⁻¹ k (double x) (c ℚ+ c) l)

\end{code}

The path from a to b.

\begin{code}

module path (a b : ℝ) (k : ℕ) (a-b-close : within (dbl^ k 1ℚ) a b) where

 M : ℚ
 M = dbl^ k 1ℚ

 private
  M-is-positive : 0ℚ < M
  M-is-positive =
   transport (_< M) (dbl^-of-zero k) (dbl^-is-monotone k 0ℚ 1ℚ 0<1)

  0≤M : ιₐ 0ℚ ≤ ιₐ M
  0≤M = ιₐ-<-gives-≤ 0ℚ M M-is-positive

  -M≤0 : ιₐ (ℚ- M) ≤ ιₐ 0ℚ
  -M≤0 = ιₐ-<-gives-≤ (ℚ- M) 0ℚ (neg-is-negative M M-is-positive)

 Hi Lo : ℝ → ℝ
 Hi x = clamp (ιₐ 0ℚ) (ιₐ M) (dbl-ℝ k x)
 Lo x = clamp (ιₐ (ℚ- M)) (ιₐ 0ℚ) (- dbl-ℝ k x)

 φ : ℝ → ℝ
 φ x = clamped-step a (Lo x) (Hi x) b

 φ-at-0 : φ (ιₐ 0ℚ) ＝ a
 φ-at-0 = clamped-step-of-zero a (Lo (ιₐ 0ℚ)) (Hi (ιₐ 0ℚ)) b I II
  where
   zero-doubled : dbl-ℝ k (ιₐ 0ℚ) ＝ ιₐ 0ℚ
   zero-doubled = dbl-ℝ-of-ιₐ k 0ℚ ∙ ap ιₐ (dbl^-of-zero k)

   II : Hi (ιₐ 0ℚ) ＝ ιₐ 0ℚ
   II = ap (clamp (ιₐ 0ℚ) (ιₐ M)) zero-doubled
      ∙ clamp-below (ιₐ 0ℚ) (ιₐ M) (ιₐ 0ℚ) (ℝ≤-refl (ιₐ 0ℚ))

   I : Lo (ιₐ 0ℚ) ＝ ιₐ 0ℚ
   I = ap (λ y → clamp (ιₐ (ℚ- M)) (ιₐ 0ℚ) (- y)) zero-doubled
     ∙ clamp-above (ιₐ (ℚ- M)) (ιₐ 0ℚ) (- ιₐ 0ℚ) -M≤0 zero-below-neg-zero

 φ-at-1 : φ (ιₐ 1ℚ) ＝ b
 φ-at-1 = clamped-step-full M a (Lo (ιₐ 1ℚ)) (Hi (ιₐ 1ℚ)) b I II a-b-close
  where
   one-doubled : dbl-ℝ k (ιₐ 1ℚ) ＝ ιₐ M
   one-doubled = dbl-ℝ-of-ιₐ k 1ℚ

   II : Hi (ιₐ 1ℚ) ＝ ιₐ M
   II = ap (clamp (ιₐ 0ℚ) (ιₐ M)) one-doubled
      ∙ clamp-above (ιₐ 0ℚ) (ιₐ M) (ιₐ M) 0≤M (ℝ≤-refl (ιₐ M))

   I : Lo (ιₐ 1ℚ) ＝ ιₐ (ℚ- M)
   I = ap (λ y → clamp (ιₐ (ℚ- M)) (ιₐ 0ℚ) (- y)) one-doubled
     ∙ clamp-below (ιₐ (ℚ- M)) (ιₐ 0ℚ) (- ιₐ M) (neg-ιₐ-≤ M)

\end{code}

A bound for the distance between two reals.

\begin{code}

reals-are-close : (a b : ℝ) → ∃ k ꞉ ℕ , within (dbl^ k 1ℚ) a b
reals-are-close a b = ∥∥-functor₂ γ
 (binary-choice (inhabited-from-real-L a) (inhabited-from-real-R a))
                                    (binary-choice (inhabited-from-real-L b)
                                      (inhabited-from-real-R b))
 where
  γ : (Σ la ꞉ ℚ , la < a) × (Σ ua ꞉ ℚ , a < ua)
    → (Σ lb ꞉ ℚ , lb < b) × (Σ ub ꞉ ℚ , b < ub)
    → Σ k ꞉ ℕ , within (dbl^ k 1ℚ) a b
  γ ((la , la<a) , (ua , a<ua)) ((lb , lb<b) , (ub , b<ub)) = k , I , II
   where
    K : ℚ
    K = ℚ-max (ub ℚ- la) (ua ℚ- lb)

    k : ℕ
    k = pr₁ (powers-of-two-are-unbounded K)

    M : ℚ
    M = dbl^ k 1ℚ

    K<M : K < M
    K<M = pr₂ (powers-of-two-are-unbounded K)

    below : (x : ℝ) (u l : ℚ) → x < u → u ℚ- l < M → (p : ℚ) → p < x
          → (p ℚ- M) < l
    below x u l m o p n = ℚ<-swap' p l M
                           (ℚ<-trans (p ℚ- l) (u ℚ- l) M
                             (ℚ<-addition-preserves-order p u (ℚ- l)
                               (cuts-are-ordered x p u n m))
                             o)

    I : (p : ℚ) → p < a → (p ℚ- M) < b
    I p n = use-rounded-real-L b (p ℚ- M) lb
             (below a ua lb a<ua (ℚ≤-<-trans (ua ℚ- lb) K M
                                   (max≤' (ub ℚ- la) (ua ℚ- lb)) K<M) p n)
             lb<b

    II : (p : ℚ) → p < b → (p ℚ- M) < a
    II p n = use-rounded-real-L a (p ℚ- M) la
              (below b ub la b<ub (ℚ≤-<-trans (ub ℚ- la) K M
                                    (max≤ (ub ℚ- la) (ua ℚ- lb)) K<M) p n)
              la<a

\end{code}

The reduction.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 approximate-IVT-from-constancy
  : (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
 approximate-IVT-from-constancy f p q a b p<q fa<q p<fb = ∥∥-rec ∃-is-prop γ p<q
  where
   γ : (Σ r ꞉ ℚ , (p < r) × (r < q)) → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
   γ (r , p<r , r<q) = ∥∥-rec ∃-is-prop δ (rounded-left-d q r r<q)
    where
     δ : (Σ s ꞉ ℚ , (r < s) × (s < q)) → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
     δ (s , r<s , s<q) = ∥∥-rec₂ ∃-is-prop ε case-a case-b
      where
       case-a : (p < f a) ∨ (f a < r)
       case-a = ∥∥-rec ∨-is-prop I
                 (rounded-right-b (upper-cut-of p) (rounded-from-real-R p) r
                   p<r)
        where
         I : (Σ r' ꞉ ℚ , (r' < r) × (p < r')) → (p < f a) ∨ (f a < r)
         I (r' , m , n) = ∥∥-functor II (ℝ-locatedness (f a) r' r m)
          where
           II : (r' < f a) ∔ (f a < r) → (p < f a) ∔ (f a < r)
           II (inl o) = inl ∣ r' , n , o ∣
           II (inr o) = inr o

       case-b : (f b < q) ∨ (s < f b)
       case-b = ∥∥-rec ∨-is-prop I (rounded-left-d q s s<q)
        where
         I : (Σ s' ꞉ ℚ , (s < s') × (s' < q)) → (f b < q) ∨ (s < f b)
         I (s' , m , n) = ∥∥-functor II (ℝ-locatedness (f b) s s' m)
          where
           II : (s < f b) ∔ (f b < s') → (f b < q) ∔ (s < f b)
           II (inl o) = inr o
           II (inr o) = inl ∣ s' , o , n ∣

       ε : (p < f a) ∔ (f a < r) → (f b < q) ∔ (s < f b)
         → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
       ε (inl l) _       = ∣ a , l , fa<q ∣
       ε (inr _) (inl l) = ∣ b , p<fb , l ∣
       ε (inr fa<r) (inr s<fb) = ∥∥-rec ∃-is-prop main (reals-are-close a b)
        where
         main : (Σ k ꞉ ℕ , within (dbl^ k 1ℚ) a b)
              → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
         main (k , close) = ∥∥-functor root
                             (normal-form ν g g-at-0 g-at-1)
          where
           open path a b k close

           gap : Σ n ꞉ ℕ , ρ n < s ℚ- r
           gap = ρ-becomes-small (s ℚ- r) (ℚ<-difference-positive r s r<s)

           n : ℕ
           n = pr₁ gap

           g : ℝ → ℝ
           g x = dbl-ℝ (succ n) (f (φ x) + ιₐ (ℚ- r))

           g-at-0 : g 0ℝ ≤ ι 1/3
           g-at-0 = transport₂ _≤_ (ap g ιₐ-zero-is-0ℝ) (ιₐ-is-ι 1/3) I
            where
             II : (f (φ (ιₐ 0ℚ)) + ιₐ (ℚ- r)) ≤ ιₐ 0ℚ
             II = translate-below (f (φ (ιₐ 0ℚ))) 0ℚ r
                   (transport (λ y → f y < 0ℚ ℚ+ r) (φ-at-0 ⁻¹)
                     (transport (f a <_) (ℚ-zero-left-neutral r ⁻¹) fa<r))

             I : g (ιₐ 0ℚ) ≤ ιₐ 1/3
             I = ℝ≤-trans (g (ιₐ 0ℚ)) (ιₐ 0ℚ) (ιₐ 1/3)
                  (transport (g (ιₐ 0ℚ) ≤_)
                    (dbl-ℝ-of-ιₐ (succ n) 0ℚ ∙ ap ιₐ (dbl^-of-zero (succ n)))
                    (dbl-ℝ-≤ (succ n) (f (φ (ιₐ 0ℚ)) + ιₐ (ℚ- r)) (ιₐ 0ℚ) II))
                  (ιₐ-<-gives-≤ 0ℚ 1/3 (0 , refl))

           g-at-1 : ι 2/3 ≤ g 1ℝ
           g-at-1 = transport₂ _≤_ (ιₐ-is-ι 2/3) (ap g (ιₐ-is-ι 1ℚ)) I
            where
             II : (s ℚ- r) < (f (φ (ιₐ 1ℚ)) + ιₐ (ℚ- r))
             II = translate-strict (f (φ (ιₐ 1ℚ))) (s ℚ- r) r
                   (transport (λ y → (s ℚ- r) ℚ+ r < f y) (φ-at-1 ⁻¹)
                     (transport (_< f b) (minus-plus s r ⁻¹) s<fb))

             III : 1ℚ < g (ιₐ 1ℚ)
             III = transport (_< g (ιₐ 1ℚ)) (dbl^-of-ρ n)
                    (below-dbl-ℝ (succ n) (f (φ (ιₐ 1ℚ)) + ιₐ (ℚ- r)) (ρ n)
                      (use-rounded-real-L (f (φ (ιₐ 1ℚ)) + ιₐ (ℚ- r)) (ρ n)
                        (s ℚ- r)
                        (pr₂ gap) II))

             I : ιₐ 2/3 ≤ g (ιₐ 1ℚ)
             I = >-gives-ιₐ-≤ (g (ιₐ 1ℚ)) 2/3
                  (use-rounded-real-L (g (ιₐ 1ℚ)) 2/3 1ℚ (0 , refl) III)

           root : (Σ x ꞉ ℝ , (0ℝ < g x) × (g x < 1ℝ))
                → Σ x ꞉ ℝ , (p < f x) × (f x < q)
           root (x , m , m') = φ x , ∣ r , p<r , r<fφx ∣ , ∣ s , fφx<s , s<q ∣
            where
             positive : 0ℚ < g x
             positive = ∥∥-rec (ℚ<ℝ-is-prop 0ℚ (g x))
                         (λ (t , o , o') → use-rounded-real-L (g x) 0ℚ t
                                            (ιₐ-upper⁻¹ 0ℚ t (transport (_< t)
                                              (ιₐ-zero-is-0ℝ ⁻¹) o)) o')
                         m

             below-one : g x < 1ℚ
             below-one = ∥∥-rec (ℝ<ℚ-is-prop (g x) 1ℚ)
                          (λ (t , o , o') → use-rounded-real-R (g x) t 1ℚ
                                             (ιₐ-lower⁻¹ t 1ℚ (transport (t <_)
                                               (ιₐ-is-ι 1ℚ ⁻¹) o')) o)
                          m'

             r<fφx : r < f (φ x)
             r<fφx = transport (_< f (φ x)) (ℚ-zero-left-neutral r)
                      (below-translate⁻¹ (f (φ x)) 0ℚ r
                        (below-dbl-ℝ⁻¹ (succ n) (f (φ x) + ιₐ (ℚ- r)) 0ℚ
                          (transport (_< g x) (dbl^-of-zero (succ n) ⁻¹)
                            positive)))

             fφx<s : f (φ x) < s
             fφx<s = transport (f (φ x) <_) (minus-plus s r)
                      (translate-below⁻¹ (f (φ x)) (s ℚ- r) r
                        (use-rounded-real-R (f (φ x) + ιₐ (ℚ- r)) (ρ n) (s ℚ- r)
                          (pr₂ gap)
                          (dbl-ℝ-below⁻¹ (succ n) (f (φ x) + ιₐ (ℚ- r)) (ρ n)
                            (transport (g x <_) (dbl^-of-ρ n ⁻¹) below-one))))

\end{code}
