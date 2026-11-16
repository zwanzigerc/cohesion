Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Limits of sequences of real numbers with a geometric modulus.

Write ρ n for the dyadic rational 2⁻⁽ⁿ⁺¹⁾, defined as ⟨1/2⟩^ (n + 1)
with ⟨1/2⟩^_ from Rationals.Limits. Two reals are within ε of each
other if each is at most the other plus ε. We state this with lower
cuts only: within ε x y says that p < x implies p - ε < y, and
p < y implies p - ε < x.

If a sequence a satisfies within (ρ (n + 1)) (a n) (a (n + 1)) for
every n, it has a limit, the real number with lower cut
{p | ∃ n , p + ρ n < a n} and upper cut {q | ∃ n , a n < q - ρ n},
and the limit is within ρ n of a n. If the sequence is eventually
constant, its limit is its eventual value; and if a n is within ρ n of
a real number y for every n, its limit is y (added on 12 November 2026
for gist.RealCohesion.DigitCurve; both are instances of
lim-from-closeness).

These are the limits used in the proof of the approximate intermediate
value theorem: the limit of the soft bisection
(gist.RealCohesion.SoftBisection) and the two clamped sums of
gist.RealCohesion.SequentialHitting.

As in gist.RealCohesion.RealLattice, we use --lossy-unification, as
TypeTopology's DedekindReals.Addition does, and the abstract copy ιₐ
of the embedding of the rationals.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealLimits
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import gist.RealCohesion.RationalArithmetic
 using (1/2≤1 ; add-difference ; <-sub-right ; <-add-right ; <-move-left ;
        <-move-right ; module halving-sequence)
open import gist.RealCohesion.RationalArithmetic using (plus-minus ; minus-plus)
 public
open import gist.RealCohesion.RationalLimits fe pe pt
 using (module halving-sequence-bounds)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above)
open import gist.RealCohesion.RealLattice fe pe pt

open PropositionalTruncation pt

\end{code}

The dyadic rationals ρ n = 2⁻⁽ⁿ⁺¹⁾.

\begin{code}

ρ : ℕ → ℚ
ρ n = ⟨1/2⟩^ (succ n)

\end{code}

ρ is a halving sequence starting at 1/2, so its lemmas are instances
of halving-sequence (gist.RealCohesion.RationalArithmetic) and
halving-sequence-bounds (gist.RealCohesion.RationalLimits).

\begin{code}

open halving-sequence ρ (λ n → refl) using () renaming (doubled to ρ-halves)
 public
open halving-sequence.positive ρ (λ n → refl) 0<1/2
 using ()
 renaming (is-positive to ρ-is-positive ; is-nonneg to ρ-is-nonneg ;
           strictly-decreases to ρ-decreases ;
            at-most-first to ρ-is-at-most-a-half ;
           antitone to ρ-antitone ; shift to ρ-shift)
 public
open halving-sequence-bounds ρ (λ n → refl) 1ℚ (ℚ<-coarser-than-≤ 0ℚ 1ℚ 0<1)
 1/2≤1
 using () renaming (becomes-small to ρ-becomes-small) public

\end{code}

Rational facts used below.

\begin{code}

minus-twice : (p ε δ : ℚ) → (p ℚ- ε) ℚ- δ ＝ p ℚ- (ε ℚ+ δ)
minus-twice p ε δ = ℚ+-assoc p (ℚ- ε) (ℚ- δ) ∙ ap (p ℚ+_) (ℚ-minus-dist ε δ)

ℚ<-add-left : (r s t : ℚ) → s < t → r ℚ+ s < r ℚ+ t
ℚ<-add-left r s t = ℚ<-addition-preserves-order''' s t r

\end{code}

Every real number has rational approximations of every positive
precision.

\begin{code}

rational-approximations-exist : (x : ℝ) (e : ℚ) → 0ℚ < e
                              → ∃ r ꞉ ℚ , ((r ℚ- e) < x) × (x < (r ℚ+ e))
rational-approximations-exist x e l =
 ∥∥-functor γ (ℝ-arithmetically-located x (e , l))
 where
  γ : (Σ (a , b) ꞉ ℚ × ℚ , ((a < x) × (x < b)) × (b ℚ- a < e))
    → Σ r ꞉ ℚ , ((r ℚ- e) < x) × (x < (r ℚ+ e))
  γ ((a , b) , (m , n) , d) =
   a ,
   use-rounded-real-L x (a ℚ- e) a (ℚ<-subtraction-preserves-order a e l) m ,
   use-rounded-real-R x b (a ℚ+ e)
    (transport (b <_) (ℚ+-comm e a) (<-move-right b e a d)) n

minus-nonneg-is-below : (p ε : ℚ) → 0ℚ ≤ ε → p ℚ- ε ≤ p
minus-nonneg-is-below p ε k =
 transport₂ _≤_ (ℚ+-comm (ℚ- ε) p) (ℚ-zero-left-neutral p)
  (ℚ≤-addition-preserves-order (ℚ- ε) 0ℚ p
    (transport (ℚ- ε ≤_) (ℚ-minus-zero-is-zero ⁻¹) (ℚ≤-swap 0ℚ ε k)))

minus-is-antitone : (p ε δ : ℚ) → ε ≤ δ → p ℚ- δ ≤ p ℚ- ε
minus-is-antitone p ε δ k =
 transport₂ _≤_ (ℚ+-comm (ℚ- δ) p) (ℚ+-comm (ℚ- ε) p)
  (ℚ≤-addition-preserves-order (ℚ- δ) (ℚ- ε) p (ℚ≤-swap ε δ k))

\end{code}

Closeness.

\begin{code}

within : ℚ → ℝ → ℝ → 𝓤₀ ̇
within ε x y = ((p : ℚ) → p < x → (p ℚ- ε) < y)
             × ((p : ℚ) → p < y → (p ℚ- ε) < x)

within-sym : (ε : ℚ) (x y : ℝ) → within ε x y → within ε y x
within-sym ε x y (f , g) = g , f

within-refl : (ε : ℚ) (x : ℝ) → 0ℚ ≤ ε → within ε x x
within-refl ε x k = I , I
 where
  I : (p : ℚ) → p < x → (p ℚ- ε) < x
  I p l = use-rounded-real-L' x (p ℚ- ε) p (minus-nonneg-is-below p ε k) l

within-trans : (ε δ : ℚ) (x y z : ℝ)
             → within ε x y → within δ y z → within (ε ℚ+ δ) x z
within-trans ε δ x y z (f , g) (f' , g') = I , II
 where
  I : (p : ℚ) → p < x → (p ℚ- (ε ℚ+ δ)) < z
  I p l = transport (_< z) (minus-twice p ε δ) (f' (p ℚ- ε) (f p l))

  II : (p : ℚ) → p < z → (p ℚ- (ε ℚ+ δ)) < x
  II p l =
   transport (_< x) (minus-twice p δ ε ∙ ap (λ t → p ℚ- t) (ℚ+-comm δ ε))
            (g (p ℚ- δ) (g' p l))

within-weaken : (ε δ : ℚ) (x y : ℝ) → ε ≤ δ → within ε x y → within δ x y
within-weaken ε δ x y k (f , g) = I , II
 where
  I : (p : ℚ) → p < x → (p ℚ- δ) < y
  I p l =
   use-rounded-real-L' y (p ℚ- δ) (p ℚ- ε) (minus-is-antitone p ε δ k) (f p l)

  II : (p : ℚ) → p < y → (p ℚ- δ) < x
  II p l =
   use-rounded-real-L' x (p ℚ- δ) (p ℚ- ε) (minus-is-antitone p ε δ k) (g p l)

within-zero : (ε u : ℚ) → 0ℚ < u → u ≤ ε → within ε (ιₐ u) (ιₐ 0ℚ)
within-zero ε u l k = I , II
 where
  ε-is-nonneg : 0ℚ ≤ ε
  ε-is-nonneg = ℚ≤-trans 0ℚ u ε (ℚ<-coarser-than-≤ 0ℚ u l) k

  I : (p : ℚ) → p < ιₐ u → (p ℚ- ε) < ιₐ 0ℚ
  I p o = ιₐ-lower (p ℚ- ε) 0ℚ
           (ℚ<-difference-positive' p ε (ℚ<-≤-trans p u ε (ιₐ-lower⁻¹ p u o) k))

  II : (p : ℚ) → p < ιₐ 0ℚ → (p ℚ- ε) < ιₐ u
  II p o = ιₐ-lower (p ℚ- ε) u
            (ℚ≤-<-trans (p ℚ- ε) p u (minus-nonneg-is-below p ε ε-is-nonneg)
              (ℚ<-trans p 0ℚ u (ιₐ-lower⁻¹ p 0ℚ o) l))

within-in-interval : (ε l r : ℚ) (x y : ℝ)
                   → r ≤ l ℚ+ ε
                   → ιₐ l ≤ x → x ≤ ιₐ r
                   → ιₐ l ≤ y → y ≤ ιₐ r
                   → within ε x y
within-in-interval ε l r x y k a b a' b' = I x y a' b , I y x a b'
 where
  I : (x y : ℝ) → ιₐ l ≤ y → x ≤ ιₐ r → (p : ℚ) → p < x → (p ℚ- ε) < y
  I x y c d p o = c (p ℚ- ε) (ιₐ-lower (p ℚ- ε) l II)
   where
    II : p ℚ- ε < l
    II = <-move-left p l ε (ℚ<-≤-trans p r (l ℚ+ ε) (ιₐ-lower⁻¹ p r (d p o)) k)

within-upper : (ε : ℚ) (x y : ℝ) → within ε x y → (q : ℚ) → x < q → y < q ℚ+ ε
within-upper ε x y (f , g) q l =
 ∥∥-rec (ℝ<ℚ-is-prop y (q ℚ+ ε)) γ
  (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) q l)
 where
  γ : (Σ q' ꞉ ℚ , (q' < q) × (x < q')) → y < q ℚ+ ε
  γ (q' , m , n) = ∥∥-rec (ℝ<ℚ-is-prop y (q ℚ+ ε)) δ
                    (ℝ-locatedness y (q' ℚ+ ε) (q ℚ+ ε)
                      (ℚ<-addition-preserves-order q' q ε m))
   where
    δ : ((q' ℚ+ ε) < y) ∔ (y < (q ℚ+ ε)) → y < q ℚ+ ε
    δ (inl o) = 𝟘-elim (not-below-and-above x q'
                         (transport (_< x) (plus-minus q' ε) (g (q' ℚ+ ε) o)) n)
    δ (inr o) = o

within-from-bound : (ε : ℚ) (x y : ℝ)
                  → y ≤ (x + ιₐ ε)
                  → (p : ℚ) → p < y → (p ℚ- ε) < x
within-from-bound ε x y k p l =
 ∥∥-rec (ℚ<ℝ-is-prop (p ℚ- ε) x) γ (below-sum⁻¹ x (ιₐ ε) p (k p l))
 where
  γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < ιₐ ε) × (p ＝ r ℚ+ s))
    → (p ℚ- ε) < x
  γ ((r , s) , m , n , e) = use-rounded-real-L x (p ℚ- ε) r o m
   where
    o : p ℚ- ε < r
    o = <-move-left p r ε
         (transport (_< r ℚ+ ε) (e ⁻¹)
           (ℚ<-add-left r s ε (ιₐ-lower⁻¹ s ε n)))

within-from-bounds : (ε : ℚ) (x y : ℝ)
                   → (x + ιₐ (ℚ- ε)) ≤ y
                   → y ≤ (x + ιₐ ε)
                   → within ε x y
within-from-bounds ε x y k k' = I , within-from-bound ε x y k'
 where
  I : (p : ℚ) → p < x → (p ℚ- ε) < y
  I p l = ∥∥-rec (ℚ<ℝ-is-prop (p ℚ- ε) y) γ (rounded-left-d x p l)
   where
    γ : (Σ p' ꞉ ℚ , (p < p') × (p' < x)) → (p ℚ- ε) < y
    γ (p' , m , n) = k (p ℚ- ε)
                      (below-sum' x (ιₐ (ℚ- ε)) (p ℚ- ε) p' ((p ℚ- ε) ℚ- p') n
                        (ιₐ-lower ((p ℚ- ε) ℚ- p') (ℚ- ε) o)
                        (add-difference p' (p ℚ- ε) ⁻¹))
     where
      o : (p ℚ- ε) ℚ- p' < ℚ- ε
      o = <-move-left (p ℚ- ε) (ℚ- ε) p'
           (transport (p ℚ- ε <_) (ℚ+-comm p' (ℚ- ε))
             (ℚ<-addition-preserves-order p p' (ℚ- ε) m))


bounds-from-within : (ε : ℚ) (x y : ℝ)
                   → within ε x y
                   → ((x + ιₐ (ℚ- ε)) ≤ y) × (y ≤ (x + ιₐ ε))
bounds-from-within ε x y (f , g) = I , II
 where
  I : (x + ιₐ (ℚ- ε)) ≤ y
  I p l = ∥∥-rec (ℚ<ℝ-is-prop p y) γ (below-sum⁻¹ x (ιₐ (ℚ- ε)) p l)
   where
    γ : (Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < ιₐ (ℚ- ε)) × (p ＝ r ℚ+ s))
      → p < y
    γ ((r , s) , m , n , e) = use-rounded-real-L y p (r ℚ- ε) o (f r m)
     where
      o : p < r ℚ- ε
      o = transport (_< r ℚ- ε) (e ⁻¹)
           (ℚ<-add-left r s (ℚ- ε) (ιₐ-lower⁻¹ s (ℚ- ε) n))

  II : y ≤ (x + ιₐ ε)
  II p l =
   ∥∥-rec (ℚ<ℝ-is-prop p (x + ιₐ ε)) γ (rounded-left-d x (p ℚ- ε) (g p l))
   where
    γ : (Σ r ꞉ ℚ , (p ℚ- ε < r) × (r < x)) → p < x + ιₐ ε
    γ (r , m , n) = below-sum' x (ιₐ ε) p r (p ℚ- r) n
                     (ιₐ-lower (p ℚ- r) ε (ℚ<-swap' p ε r m))
                     (add-difference r p ⁻¹)

\end{code}

Limits of sequences with the geometric modulus ρ.

\begin{code}

module geometric-limit
        (a : ℕ → ℝ)
        (step : (n : ℕ) → within (ρ (succ n)) (a n) (a (succ n)))
       where

 private
  telescope-step : (A C : ℚ) → (A ℚ- (C ℚ+ C)) ℚ+ C ＝ A ℚ- C
  telescope-step A C =
   (A ℚ- (C ℚ+ C)) ℚ+ C
    ＝⟨ ap (λ t → (A ℚ+ t) ℚ+ C) (ℚ-minus-dist C C ⁻¹) ⟩
   (A ℚ+ ((ℚ- C) ℚ+ (ℚ- C))) ℚ+ C  ＝⟨ ap (_ℚ+ C) (ℚ+-assoc A (ℚ- C) (ℚ- C) ⁻¹) ⟩
   ((A ℚ- C) ℚ+ (ℚ- C)) ℚ+ C       ＝⟨ ℚ+-assoc (A ℚ- C) (ℚ- C) C ⟩
   (A ℚ- C) ℚ+ ((ℚ- C) ℚ+ C)
    ＝⟨ ap ((A ℚ- C) ℚ+_) (ℚ-inverse-sum-to-zero' C) ⟩
   (A ℚ- C) ℚ+ 0ℚ                  ＝⟨ ℚ-zero-right-neutral (A ℚ- C) ⟩
   A ℚ- C                          ∎

 within-later : (n d : ℕ) → within (ρ n ℚ- ρ (n +ℕ d)) (a n) (a (n +ℕ d))
 within-later n 0        = transport (λ t → within t (a n) (a n))
                            (ℚ-inverse-sum-to-zero (ρ n) ⁻¹)
                            (within-refl 0ℚ (a n) (ℚ≤-refl 0ℚ))
 within-later n (succ d) =
  transport (λ t → within t (a n) (a (succ (n +ℕ d))))
   (ap (λ t → (ρ n ℚ- t) ℚ+ ρ (succ (n +ℕ d))) (ρ-halves (n +ℕ d) ⁻¹)
    ∙ telescope-step (ρ n) (ρ (succ (n +ℕ d))))
   (within-trans (ρ n ℚ- ρ (n +ℕ d)) (ρ (succ (n +ℕ d)))
     (a n) (a (n +ℕ d)) (a (succ (n +ℕ d)))
     (within-later n d) (step (n +ℕ d)))

 within-after : (n d : ℕ) → within (ρ n) (a n) (a (n +ℕ d))
 within-after n d = within-weaken (ρ n ℚ- ρ (n +ℕ d)) (ρ n) (a n) (a (n +ℕ d))
                     (minus-nonneg-is-below (ρ n) (ρ (n +ℕ d))
                       (ρ-is-nonneg (n +ℕ d)))
                     (within-later n d)

 within-after' : (n d : ℕ) → within (ρ n) (a n) (a (d +ℕ n))
 within-after' n d = transport (λ t → within (ρ n) (a n) (a t))
                      (addition-commutativity n d) (within-after n d)

 L U : 𝓟 ℚ
 L p = (∃ n ꞉ ℕ , (p ℚ+ ρ n) < a n) , ∃-is-prop
 U q = (∃ n ꞉ ℕ , a n < (q ℚ- ρ n)) , ∃-is-prop

 private
  inhabited-L : inhabited-left L
  inhabited-L = ∥∥-functor γ (inhabited-from-real-L (a 0))
   where
    γ : (Σ r ꞉ ℚ , r < a 0) → Σ p ꞉ ℚ , p ∈ L
    γ (r , l) =
     (r ℚ- ρ 0) , ∣ 0 , transport (_< a 0) (minus-plus r (ρ 0) ⁻¹) l ∣

  inhabited-U : inhabited-right U
  inhabited-U = ∥∥-functor γ (inhabited-from-real-R (a 0))
   where
    γ : (Σ r ꞉ ℚ , a 0 < r) → Σ q ꞉ ℚ , q ∈ U
    γ (r , l) =
     (r ℚ+ ρ 0) , ∣ 0 , transport (a 0 <_) (plus-minus r (ρ 0) ⁻¹) l ∣

  rounded-L : rounded-left L
  rounded-L p = α , β
   where
    α : p ∈ L → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
    α = ∥∥-rec ∃-is-prop γ
     where
      γ : (Σ n ꞉ ℕ , (p ℚ+ ρ n) < a n) → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
      γ (n , l) = ∥∥-functor δ (rounded-left-d (a n) (p ℚ+ ρ n) l)
       where
        δ : (Σ r ꞉ ℚ , (p ℚ+ ρ n < r) × (r < a n))
          → Σ p' ꞉ ℚ , (p < p') × p' ∈ L
        δ (r , m , m') = (r ℚ- ρ n) , <-sub-right p r (ρ n) m ,
                         ∣ n , transport (_< a n) (minus-plus r (ρ n) ⁻¹) m' ∣

    β : (∃ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
    β = ∥∥-rec ∃-is-prop γ
     where
      γ : (Σ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
      γ (p' , m , l) = ∥∥-functor δ l
       where
        δ : (Σ n ꞉ ℕ , (p' ℚ+ ρ n) < a n) → Σ n ꞉ ℕ , (p ℚ+ ρ n) < a n
        δ (n , k) = n , use-rounded-real-L (a n) (p ℚ+ ρ n) (p' ℚ+ ρ n)
                         (ℚ<-addition-preserves-order p p' (ρ n) m) k

  rounded-U : rounded-right U
  rounded-U q = α , β
   where
    α : q ∈ U → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ U
    α = ∥∥-rec ∃-is-prop γ
     where
      γ : (Σ n ꞉ ℕ , a n < (q ℚ- ρ n)) → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ U
      γ (n , l) = ∥∥-functor δ
                   (rounded-right-b (upper-cut-of (a n))
                     (rounded-from-real-R (a n))
                     (q ℚ- ρ n) l)
       where
        δ : (Σ r ꞉ ℚ , (r < q ℚ- ρ n) × (a n < r))
          → Σ q' ꞉ ℚ , (q' < q) × q' ∈ U
        δ (r , m , m') = (r ℚ+ ρ n) , <-add-right r q (ρ n) m ,
                         ∣ n , transport (a n <_) (plus-minus r (ρ n) ⁻¹) m' ∣

    β : (∃ q' ꞉ ℚ , (q' < q) × q' ∈ U) → q ∈ U
    β = ∥∥-rec ∃-is-prop γ
     where
      γ : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ U) → q ∈ U
      γ (q' , m , l) = ∥∥-functor δ l
       where
        δ : (Σ n ꞉ ℕ , a n < (q' ℚ- ρ n)) → Σ n ꞉ ℕ , a n < (q ℚ- ρ n)
        δ (n , k) = n , use-rounded-real-R (a n) (q' ℚ- ρ n) (q ℚ- ρ n)
                         (ℚ<-addition-preserves-order q' q (ℚ- ρ n) m) k

  disjoint-LU : disjoint L U
  disjoint-LU p q (l , u) = ∥∥-rec (ℚ<-is-prop p q) γ (binary-choice l u)
   where
    γ : (Σ n ꞉ ℕ , (p ℚ+ ρ n) < a n) × (Σ m ꞉ ℕ , a m < (q ℚ- ρ m)) → p < q
    γ ((n , k) , (m , k')) = cuts-are-ordered (a (m +ℕ n)) p q I II
     where
      I : p < a (m +ℕ n)
      I = transport (_< a (m +ℕ n)) (plus-minus p (ρ n))
           (pr₁ (within-after' n m) (p ℚ+ ρ n) k)

      II : a (m +ℕ n) < q
      II = transport (a (m +ℕ n) <_) (minus-plus q (ρ m))
            (within-upper (ρ m) (a m) (a (m +ℕ n)) (within-after m n) (q ℚ- ρ m)
              k')

  located-LU : located L U
  located-LU p q l = γ (ρ-becomes-small (q ℚ- p) (ℚ<-difference-positive p q l))
   where
    γ : (Σ k ꞉ ℕ , ρ k < q ℚ- p) → p ∈ L ∨ q ∈ U
    γ (k , m) = ∥∥-functor δ (ℝ-locatedness (a n) (p ℚ+ ρ n) (q ℚ- ρ n) o)
     where
      n : ℕ
      n = succ k

      o' : p ℚ+ (ρ n ℚ+ ρ n) < q
      o' = transport (λ t → p ℚ+ t < q) (ρ-halves k ⁻¹)
            (transport (_< q) (ℚ+-comm (ρ k) p) (<-add-right (ρ k) q p m))

      o : p ℚ+ ρ n < q ℚ- ρ n
      o = <-sub-right (p ℚ+ ρ n) q (ρ n)
           (transport (_< q) (ℚ+-assoc p (ρ n) (ρ n) ⁻¹) o')

      δ : ((p ℚ+ ρ n) < a n) ∔ (a n < (q ℚ- ρ n)) → p ∈ L ∔ q ∈ U
      δ (inl r) = inl ∣ n , r ∣
      δ (inr r) = inr ∣ n , r ∣

 lim : ℝ
 lim = (L , U) , inhabited-L , inhabited-U , rounded-L , rounded-U ,
                 disjoint-LU , located-LU

 lim-within : (n : ℕ) → within (ρ n) lim (a n)
 lim-within n = I , II
  where
   I : (p : ℚ) → p < lim → (p ℚ- ρ n) < a n
   I p = ∥∥-rec (ℚ<ℝ-is-prop (p ℚ- ρ n) (a n)) γ
    where
     γ : (Σ k ꞉ ℕ , (p ℚ+ ρ k) < a k) → (p ℚ- ρ n) < a n
     γ (k , l) = pr₂ (within-after' n k) p
                  (transport (_< a (k +ℕ n)) (plus-minus p (ρ k))
                    (pr₁ (within-after k n) (p ℚ+ ρ k) l))

   II : (p : ℚ) → p < a n → (p ℚ- ρ n) < lim
   II p l = ∣ n , transport (_< a n) (minus-plus p (ρ n) ⁻¹) l ∣

 lim-from-closeness : (y : ℝ) (N : ℕ)
                    → ((d : ℕ) → within (ρ (d +ℕ N)) lim y)
                    → lim ＝ y
 lim-from-closeness y N close = equal-if-lower-cuts-agree lim y I II
  where
   small : (ε : ℚ) → 0ℚ < ε → Σ d ꞉ ℕ , ρ (d +ℕ N) < ε
   small ε l = d , ℚ≤-<-trans (ρ (d +ℕ N)) (ρ d) ε (ρ-shift d N)
                    (pr₂ (ρ-becomes-small ε l))
    where
     d : ℕ
     d = pr₁ (ρ-becomes-small ε l)

   transfer : (x x' : ℝ) → ((d : ℕ) → within (ρ (d +ℕ N)) x x')
            → lower-cut-of x ⊆ lower-cut-of x'
   transfer x x' c p l = ∥∥-rec (ℚ<ℝ-is-prop p x') γ (rounded-left-d x p l)
    where
     γ : (Σ r ꞉ ℚ , (p < r) × (r < x)) → p < x'
     γ (r , m , n) = use-rounded-real-L x' p (r ℚ- ρ (d +ℕ N)) o
                      (pr₁ (c d) r n)
      where
       d : ℕ
       d = pr₁ (small (r ℚ- p) (ℚ<-difference-positive p r m))

       o : p < r ℚ- ρ (d +ℕ N)
       o = <-sub-right p r (ρ (d +ℕ N))
            (transport (_< r) (ℚ+-comm (ρ (d +ℕ N)) p)
              (<-add-right (ρ (d +ℕ N)) r p
                (pr₂ (small (r ℚ- p) (ℚ<-difference-positive p r m)))))

   I : lower-cut-of lim ⊆ lower-cut-of y
   I = transfer lim y close

   II : lower-cut-of y ⊆ lower-cut-of lim
   II = transfer y lim (λ d → within-sym (ρ (d +ℕ N)) lim y (close d))

 lim-of-eventually-constant : (y : ℝ) (N : ℕ)
                            → ((d : ℕ) → a (N +ℕ d) ＝ y)
                            → lim ＝ y
 lim-of-eventually-constant y N e = lim-from-closeness y N close
  where
   close : (d : ℕ) → within (ρ (d +ℕ N)) lim y
   close d = transport (λ t → within (ρ (d +ℕ N)) lim t)
              (ap a (addition-commutativity d N) ∙ e d)
              (lim-within (d +ℕ N))

 lim-of-approximations : (y : ℝ) → ((n : ℕ) → within (ρ n) (a n) y) → lim ＝ y
 lim-of-approximations y c = lim-from-closeness y 0 close
  where
   close : (d : ℕ) → within (ρ d) lim y
   close d = transport (λ ε → within ε lim y) (ρ-halves d)
              (within-trans (ρ (succ d)) (ρ (succ d)) lim (a (succ d)) y
                (lim-within (succ d)) (c (succ d)))

\end{code}

Clamped steps. A clamped step from x towards t moves to t when t is
in [x + lo , x + hi], and in any case stays in that interval. The two
sums of gist.RealCohesion.SequentialHitting are built from such steps,
so that no subtraction of reals is needed.

\begin{code}

clamped-step : ℝ → ℝ → ℝ → ℝ → ℝ
clamped-step x lo hi t = clamp (x + lo) (x + hi) t

clamped-step-of-zero : (x lo hi t : ℝ)
                     → lo ＝ ιₐ 0ℚ
                     → hi ＝ ιₐ 0ℚ
                     → clamped-step x lo hi t ＝ x
clamped-step-of-zero x lo hi t e e' =
 transport₂ (λ l h → clamp (x + l) (x + h) t ＝ x) (e ⁻¹) (e' ⁻¹) I
 where
  I : clamp (x + ιₐ 0ℚ) (x + ιₐ 0ℚ) t ＝ x
  I = clamp-degenerate (x + ιₐ 0ℚ) t ∙ plus-zero x

clamped-step-full : (ε : ℚ) (x lo hi t : ℝ)
                  → lo ＝ ιₐ (ℚ- ε)
                  → hi ＝ ιₐ ε
                  → within ε x t
                  → clamped-step x lo hi t ＝ t
clamped-step-full ε x lo hi t e e' c =
 transport₂ (λ l h → clamp (x + l) (x + h) t ＝ t) (e ⁻¹) (e' ⁻¹) I
 where
  I : clamp (x + ιₐ (ℚ- ε)) (x + ιₐ ε) t ＝ t
  I = clamp-inside (x + ιₐ (ℚ- ε)) (x + ιₐ ε) t
       (pr₁ (bounds-from-within ε x t c)) (pr₂ (bounds-from-within ε x t c))

clamped-step-within : (ε : ℚ) (x lo hi t : ℝ)
                    → ιₐ (ℚ- ε) ≤ lo
                    → lo ≤ hi
                    → hi ≤ ιₐ ε
                    → within ε x (clamped-step x lo hi t)
clamped-step-within ε x lo hi t k k' k'' =
 within-from-bounds ε x (clamped-step x lo hi t) I II
 where
  I : (x + ιₐ (ℚ- ε)) ≤ clamped-step x lo hi t
  I = ℝ≤-trans (x + ιₐ (ℚ- ε)) (x + lo) (clamped-step x lo hi t)
       (sum-≤ x x (ιₐ (ℚ- ε)) lo (ℝ≤-refl x) k)
       (clamp-is-above-lo (x + lo) (x + hi) t)

  II : clamped-step x lo hi t ≤ (x + ιₐ ε)
  II = ℝ≤-trans (clamped-step x lo hi t) (x + hi) (x + ιₐ ε)
        (clamp-is-below-hi (x + lo) (x + hi) t (sum-≤ x x lo hi (ℝ≤-refl x) k'))
        (sum-≤ x x hi (ιₐ ε) (ℝ≤-refl x) k'')

\end{code}
