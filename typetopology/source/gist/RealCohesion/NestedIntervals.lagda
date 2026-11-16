Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The real number determined by nested rational intervals.

Let [x n , x n + d n] be rational intervals such that each contains the
next and whose lengths d n ≥ 0 become arbitrarily small. They determine
a Dedekind real t, with lower cut {r | ∃ n , r < x n} and upper cut
{r | ∃ n , x n + d n < r}. Every rational interval around t contains
one of the given intervals. The construction is constructive; it is
used in gist.RealCohesion.CrispConnectedness for limits of bisections,
and in gist.RealCohesion.CrispBolzanoWeierstrass, coordinate by
coordinate, for limits of nested cubes.
We allow intervals of length 0, so that the limit of a bisection of a
crisp interval [α , β] can be formed without a proof of α < β.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.NestedIntervals
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order
open import Notation.Order
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Powerset
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.RationalArithmetic using (monotone-from-steps)

open PropositionalTruncation pt

\end{code}

The data.

\begin{code}

record Nested-Intervals : 𝓤₀ ̇ where
 field
  left       : ℕ → ℚ
  length     : ℕ → ℚ
  length-nonneg : (n : ℕ) → 0ℚ ≤ length n
  left-grows : (n : ℕ) → left n ≤ left (succ n)
  right-shrinks : (n : ℕ) → left (succ n) + length (succ n) ≤ left n + length n
  lengths-become-small : (ε : ℚ) → 0ℚ < ε → Σ n ꞉ ℕ , length n < ε

module _ (𝓘 : Nested-Intervals) where

 open Nested-Intervals 𝓘

 right : ℕ → ℚ
 right n = left n + length n

 left-below-right : (n : ℕ) → left n ≤ right n
 left-below-right n =
  ℚ≤-addition-preserves-order'' (left n) (length n) (length-nonneg n)

 left-grows-≤ : (n k : ℕ) → n ≤ k → left n ≤ left k
 left-grows-≤ =
  monotone-from-steps (λ u v → u ≤ v) ℚ≤-refl ℚ≤-trans left left-grows

 right-shrinks-≤ : (n k : ℕ) → n ≤ k → right k ≤ right n
 right-shrinks-≤ = monotone-from-steps (λ u v → v ≤ u) ℚ≤-refl
                    (λ u v w p q → ℚ≤-trans w v u q p) right right-shrinks

 left-below-every-right : (n m : ℕ) → left n ≤ right m
 left-below-every-right n m =
  ℚ≤-trans (left n) (left (n ℕ+ m)) (right m)
   (left-grows-≤ n (n ℕ+ m) (≤-+ n m))
   (ℚ≤-trans (left (n ℕ+ m)) (right (n ℕ+ m)) (right m)
     (left-below-right (n ℕ+ m))
     (right-shrinks-≤ m (n ℕ+ m) (≤-+' n m)))

\end{code}

The cuts.

\begin{code}

 L R : 𝓟 ℚ
 L r = (∃ n ꞉ ℕ , r < left n) , ∃-is-prop
 R r = (∃ n ꞉ ℕ , right n < r) , ∃-is-prop

 L-is-inhabited : inhabited-left L
 L-is-inhabited = ∣ pr₁ (ℚ-no-least-element (left 0)) ,
                    ∣ 0 , pr₂ (ℚ-no-least-element (left 0)) ∣ ∣

 R-is-inhabited : inhabited-right R
 R-is-inhabited = ∣ pr₁ (ℚ-no-max-element (right 0)) ,
                    ∣ 0 , pr₂ (ℚ-no-max-element (right 0)) ∣ ∣

 L-is-rounded : rounded-left L
 L-is-rounded r = α , β
  where
   α : r ∈ L → ∃ p ꞉ ℚ , (r < p) × p ∈ L
   α = ∥∥-functor γ
    where
     γ : (Σ n ꞉ ℕ , r < left n) → Σ p ꞉ ℚ , (r < p) × p ∈ L
     γ (n , l) = pr₁ (ℚ-dense r (left n) l) ,
                 pr₁ (pr₂ (ℚ-dense r (left n) l)) ,
                 ∣ n , pr₂ (pr₂ (ℚ-dense r (left n) l)) ∣

   β : (∃ p ꞉ ℚ , (r < p) × p ∈ L) → r ∈ L
   β = ∥∥-rec (∈-is-prop L r) γ
    where
     γ : (Σ p ꞉ ℚ , (r < p) × p ∈ L) → r ∈ L
     γ (p , l , m) = ∥∥-functor (λ (n , k) → n , ℚ<-trans r p (left n) l k) m

 R-is-rounded : rounded-right R
 R-is-rounded r = α , β
  where
   α : r ∈ R → ∃ q ꞉ ℚ , (q < r) × q ∈ R
   α = ∥∥-functor γ
    where
     γ : (Σ n ꞉ ℕ , right n < r) → Σ q ꞉ ℚ , (q < r) × q ∈ R
     γ (n , l) = pr₁ (ℚ-dense (right n) r l) ,
                 pr₂ (pr₂ (ℚ-dense (right n) r l)) ,
                 ∣ n , pr₁ (pr₂ (ℚ-dense (right n) r l)) ∣

   β : (∃ q ꞉ ℚ , (q < r) × q ∈ R) → r ∈ R
   β = ∥∥-rec (∈-is-prop R r) γ
    where
     γ : (Σ q ꞉ ℚ , (q < r) × q ∈ R) → r ∈ R
     γ (q , l , m) = ∥∥-functor (λ (n , k) → n , ℚ<-trans (right n) q r k l) m

 L-R-are-disjoint : disjoint L R
 L-R-are-disjoint p q (a , b) = ∥∥-rec (ℚ<-is-prop p q) γ a
  where
   γ : (Σ n ꞉ ℕ , p < left n) → p < q
   γ (n , l) = ∥∥-rec (ℚ<-is-prop p q) δ b
    where
     δ : (Σ m ꞉ ℕ , right m < q) → p < q
     δ (m , k) = ℚ<-trans p (right m) q
                  (ℚ<-≤-trans p (left n) (right m) l
                    (left-below-every-right n m))
                  k

 L-R-are-located : located L R
 L-R-are-located p q l =
  γ (lengths-become-small (q - p) (ℚ<-difference-positive p q l))
  where
   γ : (Σ n ꞉ ℕ , length n < q - p) → p ∈ L ∨ q ∈ R
   γ (n , k) = δ (ℚ-dichotomous' p (left n))
    where
     δ : (p < left n) ∔ (left n ≤ p) → p ∈ L ∨ q ∈ R
     δ (inl m) = ∣ inl ∣ n , m ∣ ∣
     δ (inr m) = ∣ inr ∣ n , ε ∣ ∣
      where
       I : length n + p < q
       I = ℚ<-subtraction-preserves-order'' (length n) q p k

       II : p + length n < q
       II = transport (_< q) (ℚ+-comm (length n) p) I

       ε : right n < q
       ε = ℚ≤-<-trans (right n) (p + length n) q
            (ℚ≤-addition-preserves-order (left n) p (length n) m)
            II

\end{code}

The limit, and its properties.

\begin{code}

 limit : ℝ
 limit = (L , R) , L-is-inhabited , R-is-inhabited , L-is-rounded , R-is-rounded
                 , L-R-are-disjoint , L-R-are-located

 below-the-limit : (n : ℕ) (r : ℚ) → r < left n → r < limit
 below-the-limit n r l = ∣ n , l ∣

 above-the-limit : (n : ℕ) (r : ℚ) → right n < r → limit < r
 above-the-limit n r l = ∣ n , l ∣

 below-the-limit-gives-below-right : (n : ℕ) (r : ℚ) → r < limit → r < right n
 below-the-limit-gives-below-right n r = ∥∥-rec (ℚ<-is-prop r (right n)) γ
  where
   γ : (Σ k ꞉ ℕ , r < left k) → r < right n
   γ (k , l) = ℚ<-≤-trans r (left k) (right n) l (left-below-every-right k n)

 intervals-around-the-limit : (r r' : ℚ)
                            → r < limit
                            → limit < r'
                            → ∃ n ꞉ ℕ , (r < left n) × (right n < r')
 intervals-around-the-limit r r' a b = ∥∥-rec ∃-is-prop γ a
  where
   γ : (Σ n ꞉ ℕ , r < left n) → ∃ n ꞉ ℕ , (r < left n) × (right n < r')
   γ (n , l) = ∥∥-functor δ b
    where
     δ : (Σ m ꞉ ℕ , right m < r') → Σ k ꞉ ℕ , (r < left k) × (right k < r')
     δ (m , k) = (n ℕ+ m) ,
                 ℚ<-≤-trans r (left n) (left (n ℕ+ m)) l
                  (left-grows-≤ n (n ℕ+ m) (≤-+ n m)) ,
                 ℚ≤-<-trans (right (n ℕ+ m)) (right m) r'
                  (right-shrinks-≤ m (n ℕ+ m) (≤-+' n m)) k

\end{code}
