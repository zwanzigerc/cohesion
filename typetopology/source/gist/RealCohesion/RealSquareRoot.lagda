Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Square roots of nonnegative real numbers (gate G14, step E4).

The definition is transcribed from agda-unimath, module
real-numbers.square-roots-nonnegative-real-numbers, at commit 7551865
(MIT licence, a copy of which is LICENSE-agda-unimath.md beside this
module). The lower cut of √x is the set of rationals q such that q² < x
if q ≥ 0, and its upper cut is the set of positive rationals q with
x < q². agda-unimath defines it for x ≥ 0; the cuts are cuts for every
real x, so we define square-root on all of ℝ, where it is 0 at
negative x, and assume x ≥ 0 only in the square law. The roundedness
and inhabitedness of the cuts use the facts on rational squares of
gist.RealCohesion.RationalProducts (square-rounds-up,
square-rounds-down, square-above) in place of agda-unimath's lemmas on
positive rationals.

The properties are those of agda-unimath's module that the sphere of
gist.RealCohesion.EuclideanSphere uses, with our own proofs, since our
multiplication is that of gist.RealCohesion.RealMultiplication and not
agda-unimath's:

 * √x ≥ 0 (square-root-is-nonneg);

 * √x √x = x for x ≥ 0 (square-root-squared). If q < √x √x, then q < m²
   for every rational m in some interval (a , b) around √x
   (below-square⁻¹), and a rational m in (a , √x) has m² < x if m ≥ 0,
   while a negative one puts 0 in (a , b), so that q < 0. If
   √x √x < r < x, then m² < r for every rational m in some interval
   (a , b) around √x, and a rational m in (√x , b) has x < m². This is
   agda-unimath's argument, with the interval around √x in place of the
   enclosing intervals of its products;

 * squares are strictly monotone on nonnegative reals, so nonnegative
   square roots are unique (nonneg-square-roots-are-unique), and
   √(s s) = s for s ≥ 0 (square-root-of-square).

Two further facts, not from agda-unimath's module, are used by the
sphere: a product of nonnegative reals is nonnegative
(products-of-nonnegatives-are-nonneg), and a real whose square is at
most 0 is 0 (square-at-most-zero).

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealSquareRoot
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.Order
open import UF.Base
open import UF.Powerset
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier using (holds-is-prop)
open import Rationals.Type
open import Rationals.Order
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalArithmetic using (neg-is-negative)
open import gist.RealCohesion.RationalProducts
 using
  (square-rounds-up ; square-rounds-down ; square-above ; square-below-square ;
   negative-rounds-up ; negation-times-negation ; negative-gives-positive)
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; ℝ<-tight)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; ℝ<ℚ-is-prop ; ≤-<-trans-ℚ ; 0ℝ-below-positive⁻¹)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using (_*_ ; Interval-Above-Square ; Interval-Below-Square ; below-square⁻¹ ;
        square-below⁻¹ ; products-above ; products-below ;
         <-from-rational-between ;
        squares-are-nonneg ; products-of-negatives-above ;
         product-of-positives-is-positive)
open import gist.RealCohesion.RealAlgebra fe pe pt using (square-of-scaled)

open PropositionalTruncation pt

\end{code}

The definition.

\begin{code}

square-root : ℝ → ℝ
square-root x = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R ,
                disjoint-LR , located-LR
 where
  L R : 𝓟 ℚ
  L p = (0ℚ ≤ p → (p ℚ* p) < x) , Π-is-prop fe (λ _ → ℚ<ℝ-is-prop (p ℚ* p) x)
  R q = ((0ℚ < q) × (x < (q ℚ* q))) ,
         ×-is-prop (ℚ<-is-prop 0ℚ q) (ℝ<ℚ-is-prop x (q ℚ* q))

  not-nonneg : (p : ℚ) → p < 0ℚ → ¬ (0ℚ ≤ p)
  not-nonneg p l k = ℚ<-irrefl 0ℚ (ℚ≤-<-trans 0ℚ p 0ℚ k l)

  inhabited-L : inhabited-left L
  inhabited-L =
   ∣ ℚ- 1ℚ , (λ k → 𝟘-elim (not-nonneg (ℚ- 1ℚ) (neg-is-negative 1ℚ 0<1) k)) ∣

  inhabited-R : inhabited-right R
  inhabited-R = ∥∥-functor γ (inhabited-from-real-R x)
   where
    γ : (Σ u ꞉ ℚ , x < u) → Σ q ꞉ ℚ , q ∈ R
    γ (u , l) = pr₁ m , pr₁ (pr₂ m) ,
                 use-rounded-real-R' x u (pr₁ m ℚ* pr₁ m) (pr₂ (pr₂ m)) l
     where
      m : Σ m ꞉ ℚ , (0ℚ < m) × (u ≤ m ℚ* m)
      m = square-above u

  rounded-L : rounded-left L
  rounded-L p = α , β
   where
    α : p ∈ L → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
    α h = Cases (ℚ-dichotomous' p 0ℚ) negative nonneg
     where
      negative : p < 0ℚ → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
      negative l = ∣ pr₁ d , pr₁ (pr₂ d) ,
                    (λ k → 𝟘-elim (not-nonneg (pr₁ d) (pr₂ (pr₂ d)) k)) ∣
       where
        d : Σ p' ꞉ ℚ , (p < p') × (p' < 0ℚ)
        d = negative-rounds-up p l

      nonneg : 0ℚ ≤ p → ∃ p' ꞉ ℚ , (p < p') × p' ∈ L
      nonneg k = ∥∥-functor γ (rounded-left-d x (p ℚ* p) (h k))
       where
        γ : (Σ s ꞉ ℚ , (p ℚ* p < s) × (s < x)) → Σ p' ꞉ ℚ , (p < p') × p' ∈ L
        γ (s , m , n) = pr₁ u , pr₁ (pr₂ u) ,
                        (λ _ → use-rounded-real-L x (pr₁ u ℚ* pr₁ u) s
                                (pr₂ (pr₂ u)) n)
         where
          u : Σ p' ꞉ ℚ , (p < p') × (p' ℚ* p' < s)
          u = square-rounds-up p s k m

    β : (∃ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
    β = ∥∥-rec (holds-is-prop (L p)) γ
     where
      γ : (Σ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
      γ (p' , m , h) k = use-rounded-real-L x (p ℚ* p) (p' ℚ* p')
                          (square-below-square p p' k m)
                          (h (ℚ≤-trans 0ℚ p p' k (ℚ<-coarser-than-≤ p p' m)))

  rounded-R : rounded-right R
  rounded-R q = α , β
   where
    α : q ∈ R → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ R
    α (k , l) = ∥∥-functor γ
     (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) (q ℚ* q) l)
     where
      γ : (Σ s ꞉ ℚ , (s < q ℚ* q) × (x < s)) → Σ q' ꞉ ℚ , (q' < q) × q' ∈ R
      γ (s , m , n) = pr₁ u , pr₁ (pr₂ (pr₂ u)) , pr₁ (pr₂ u) ,
                      use-rounded-real-R x s (pr₁ u ℚ* pr₁ u)
                       (pr₂ (pr₂ (pr₂ u))) n
       where
        u : Σ q' ꞉ ℚ , (0ℚ < q') × (q' < q) × (s < q' ℚ* q')
        u = square-rounds-down q s k m

    β : (∃ q' ꞉ ℚ , (q' < q) × q' ∈ R) → q ∈ R
    β = ∥∥-rec (holds-is-prop (R q)) γ
     where
      γ : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ R) → q ∈ R
      γ (q' , m , k , l) = ℚ<-trans 0ℚ q' q k m ,
                           use-rounded-real-R x (q' ℚ* q') (q ℚ* q)
                            (square-below-square q' q
                              (ℚ<-coarser-than-≤ 0ℚ q' k) m) l

  disjoint-LR : disjoint L R
  disjoint-LR p q (h , k , l) = Cases (ℚ-dichotomous' p 0ℚ) negative nonneg
   where
    negative : p < 0ℚ → p < q
    negative m = ℚ<-trans p 0ℚ q m k

    nonneg : 0ℚ ≤ p → p < q
    nonneg n = Cases (ℚ-dichotomous' p q) id I
     where
      squares : p ℚ* p < q ℚ* q
      squares = cuts-are-ordered x (p ℚ* p) (q ℚ* q) (h n) l

      I : q ≤ p → p < q
      I o = 𝟘-elim (Cases (ℚ≤-split q p o) II III)
       where
        II : q < p → 𝟘
        II r = ℚ<-irrefl (p ℚ* p) (ℚ<-trans (p ℚ* p) (q ℚ* q) (p ℚ* p) squares
                 (square-below-square q p (ℚ<-coarser-than-≤ 0ℚ q k) r))

        III : q ＝ p → 𝟘
        III e = ℚ<-irrefl (p ℚ* p) (transport (λ - → p ℚ* p < - ℚ* -) e squares)

  located-LR : located L R
  located-LR p q m = Cases (ℚ-dichotomous' p 0ℚ) negative nonneg
   where
    negative : p < 0ℚ → p ∈ L ∨ q ∈ R
    negative l = ∣ inl (λ k → 𝟘-elim (not-nonneg p l k)) ∣

    nonneg : 0ℚ ≤ p → p ∈ L ∨ q ∈ R
    nonneg k = ∥∥-functor γ
     (ℝ-locatedness x (p ℚ* p) (q ℚ* q) (square-below-square p q k m))
     where
      γ : (p ℚ* p < x) ∔ (x < q ℚ* q) → p ∈ L ∔ q ∈ R
      γ (inl l) = inl (λ _ → l)
      γ (inr l) = inr (ℚ≤-<-trans 0ℚ p q k m , l)

\end{code}

The square root is nonnegative, and its square is x where x ≥ 0.

\begin{code}

square-root-is-nonneg : (x : ℝ) → 0ℝ ≤ square-root x
square-root-is-nonneg x p l k = 𝟘-elim (ℚ<-irrefl 0ℚ (ℚ≤-<-trans 0ℚ p 0ℚ k l))

square-root-squared : (x : ℝ) → 0ℝ ≤ x → square-root x * square-root x ＝ x
square-root-squared x k = ℝ<-tight (s * s) x not-below not-above
 where
  s : ℝ
  s = square-root x

  at-most : (s * s) ≤ x
  at-most q l = Cases (ℚ-dichotomous' q 0ℚ) negative nonneg
   where
    negative : q < 0ℚ → q < x
    negative m = k q m

    nonneg : 0ℚ ≤ q → q < x
    nonneg n = ∥∥-rec (ℚ<ℝ-is-prop q x) γ (below-square⁻¹ q s l)
     where
      γ : Interval-Above-Square q s → q < x
      γ (a , b , o , o' , w) = ∥∥-rec (ℚ<ℝ-is-prop q x) δ (rounded-left-d s a o)
       where
        δ : (Σ m ꞉ ℚ , (a < m) × (m < s)) → q < x
        δ (m , r , r') = Cases (ℚ-dichotomous' m 0ℚ) I II
         where
          I : m < 0ℚ → q < x
          I t = 𝟘-elim (ℚ<-irrefl 0ℚ (ℚ≤-<-trans 0ℚ q 0ℚ n III))
           where
            III : q < 0ℚ
            III = transport (q <_) (ℚ-zero-left-is-zero 0ℚ)
                   (w 0ℚ (ℚ<-trans a m 0ℚ r t) (pr₁ o'))

          II : 0ℚ ≤ m → q < x
          II t = use-rounded-real-L x q (m ℚ* m)
                  (w m r (cuts-are-ordered s m b r' o')) (r' t)

  not-above : ¬ (x < s * s)
  not-above = ℝ-less-than-or-equal-not-greater (s * s) x at-most

  not-below : ¬ (s * s < x)
  not-below l = ∥∥-rec 𝟘-is-prop γ l
   where
    γ : (Σ r ꞉ ℚ , (s * s < r) × (r < x)) → 𝟘
    γ (r , o , o') = ∥∥-rec 𝟘-is-prop δ (square-below⁻¹ r s o)
     where
      δ : Interval-Below-Square r s → 𝟘
      δ (a , b , t , t' , w) =
       ∥∥-rec 𝟘-is-prop ε
        (rounded-right-b (upper-cut-of s) (rounded-from-real-R s) b t')
       where
        ε : (Σ m ꞉ ℚ , (m < b) × (s < m)) → 𝟘
        ε (m , u , u') = ℚ<-irrefl r (ℚ<-trans r (m ℚ* m) r
                          (cuts-are-ordered x r (m ℚ* m) o' (pr₂ u'))
                          (w m (cuts-are-ordered s a m t u') u))

\end{code}

Squares are strictly monotone on nonnegative reals: for a rational p
with s < p < t, s s < p p < t t. Hence nonnegative square roots are
unique, and the square root of s s is s for s ≥ 0.

\begin{code}

squares-are-strictly-monotone : (s t : ℝ) → 0ℝ ≤ s → s < t → s * s < t * t
squares-are-strictly-monotone s t k l = ∥∥-rec (<-is-prop (s * s) (t * t)) γ l
 where
  γ : (Σ p ꞉ ℚ , (s < p) × (p < t)) → s * s < t * t
  γ (p , m , n) = <-from-rational-between (s * s) (t * t) (p ℚ* p)
                   (products-below p s s I m I m)
                   (products-above p p t t p-is-positive p-is-positive n n)
   where
    p-is-positive : 0ℚ < p
    p-is-positive = 0ℝ-below-positive⁻¹ p (≤-<-trans-ℚ 0ℝ s p k m)

    I : (ℚ- p) < s
    I = k (ℚ- p) (neg-is-negative p p-is-positive)

nonneg-square-roots-are-unique : (s t : ℝ) → 0ℝ ≤ s → 0ℝ ≤ t → s * s ＝ t * t
                               → s ＝ t
nonneg-square-roots-are-unique s t k k' e = ℝ<-tight s t I II
 where
  I : ¬ (s < t)
  I l = <ℝ-irreflexive (s * s)
         (transport (s * s <_) (e ⁻¹) (squares-are-strictly-monotone s t k l))

  II : ¬ (t < s)
  II l = <ℝ-irreflexive (t * t)
          (transport (t * t <_) e (squares-are-strictly-monotone t s k' l))

square-root-of-square : (s : ℝ) → 0ℝ ≤ s → square-root (s * s) ＝ s
square-root-of-square s k =
 nonneg-square-roots-are-unique (square-root (s * s)) s
  (square-root-is-nonneg (s * s)) k
  (square-root-squared (s * s) (squares-are-nonneg s))

\end{code}

Two facts that the sphere uses: a product of nonnegative reals is
nonnegative, as the square of the product of their square roots; and a
real whose square is at most 0 is 0, since the square of a positive or
of a negative real is positive.

\begin{code}

products-of-nonnegatives-are-nonneg : (x y : ℝ) → 0ℝ ≤ x → 0ℝ ≤ y → 0ℝ ≤ x * y
products-of-nonnegatives-are-nonneg x y k k' =
 transport (0ℝ ≤_) I (squares-are-nonneg (a * b))
 where
  a b : ℝ
  a = square-root x
  b = square-root y

  I : (a * b) * (a * b) ＝ x * y
  I = square-of-scaled a b
      ∙ ap₂ _*_ (square-root-squared x k) (square-root-squared y k')

square-at-most-zero : (x : ℝ) → x * x ≤ 0ℝ → x ＝ 0ℝ
square-at-most-zero x k = ℝ<-tight x 0ℝ I II
 where
  not-positive : ¬ (0ℝ < x * x)
  not-positive = ℝ-less-than-or-equal-not-greater (x * x) 0ℝ k

  I : ¬ (x < 0ℝ)
  I l = ∥∥-rec 𝟘-is-prop γ l
   where
    γ : (Σ b ꞉ ℚ , (x < b) × (b < 0ℝ)) → 𝟘
    γ (b , m , n) = not-positive
                     (<-from-rational-between 0ℝ (x * x) (b ℚ* b) III
                       (products-of-negatives-above b b x x n n m m))
     where
      III : 0ℚ < b ℚ* b
      III = transport (0ℚ <_) (negation-times-negation b b)
             (ℚ<-pos-multiplication-preserves-order (ℚ- b) (ℚ- b)
               (negative-gives-positive b n) (negative-gives-positive b n))

  II : ¬ (0ℝ < x)
  II l = not-positive (product-of-positives-is-positive x x l l)

\end{code}
