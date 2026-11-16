Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The reciprocal of max(1 , s) for real numbers s (gate G14, step E1).

This is the division that the retraction of ℝⁿ onto the Euclidean
ball needs: the retraction x ↦ x / max(1 , ‖x‖²) of Fable's addendum
(ADDENDUM-2, G14), which needs no square root; Codex audited it on
12 November 2026. The function s ↦ 1 / max(1 , s) is the continuous
extension, by gist.RealCohesion.RationalBoxExtension, of its rational
version reciprocal of gist.RealCohesion.RationalProducts, which is
1-Lipschitz. It agrees with reciprocal at rational points and is
continuous; it is at most 1, it is 1 where s ≤ 1, and
s (1 / max(1 , s))² ≤ 1. Scaled, it gives the inverse of every positive
real number (gate G14, step E4), at the end of the module.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RealReciprocal
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.Order
open import UF.Base
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (Coordinatewise-Strictly-Continuous)
open import gist.RealCohesion.RationalArithmetic using (abs-gives-ball)
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-lower ; ιₐ-upper ; ιₐ-lower⁻¹ ; ιₐ-upper⁻¹)
open import gist.RealCohesion.RationalProducts
 using
  (interval-gives-close ; widened-point ; reciprocal ; reciprocal-is-Lipschitz ;
   reciprocal-of-at-most-one ; reciprocal-bound ; reciprocal-≤-one ;
    point-at-most-one ;
   reciprocal-is-nonneg ; times-reciprocal-of-at-least-one ;
    times-reciprocal-≤-one)
open import gist.RealCohesion.RealBalls fe pe pt
 using (Close-from-interval ; halfₐ ; quarter-is-positive ; twice-a-quarter)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ιₐ-≤-ιₐ ; <-≤-trans-ℚ ; 0ℝ-below-positive⁻¹)
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above ; ℝ<-tight ; ℝ≤-refl)
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (In-Box ; Around ; Small-Box ; small-box-around ; rational-point-in-box ;
        common-point ; module extension-from-samples ;
         composition-is-continuous ;
        projection-is-continuous ; constant-is-continuous ;
         ≤-at-a-continuity-point ;
        ≤-near-a-continuity-point)
open import gist.RealCohesion.RealMultiplication fe pe pt
 using
  (_*_ ; ιₐ-* ; product-is-continuous ; 1ℝ-is-ιₐ ; 0ℝ-is-ιₐ ; *-assoc ; *-comm ;
   *-right-unit ; *-left-unit ; products-above)

open PropositionalTruncation pt

\end{code}

The sample points are the rational points of ℚ¹, with value the
reciprocal. Around a real point, the reciprocals at the rational points
of an interval shorter than η = ε/4 differ by less than η, because the
reciprocal is 1-Lipschitz, and so lie in an interval of length 2η < ε.

\begin{code}

reciprocal-at : (Fin 1 → ℚ) → ℝ
reciprocal-at c = ιₐ (reciprocal (c 𝟎))

open extension-from-samples {1} (Fin 1 → ℚ) id reciprocal-at
 rational-point-in-box common-point

reciprocals-vary-little : Has-Small-Oscillation
reciprocals-vary-little x ε l =
 ∥∥-functor γ (small-box-around x η η-is-positive)
 where
  η : ℚ
  η = halfₐ (halfₐ ε)

  η-is-positive : 0ℚ < η
  η-is-positive = quarter-is-positive ε l

  γ : Small-Box x η
    → Σ (a , b) ꞉ (Fin 1 → ℚ) × (Fin 1 → ℚ) ,
        Around a b x × Small-Oscillation ε a b
  γ ((a , b) , m , w) = (a , b) , m , oscillation
   where
    oscillation : Small-Oscillation ε a b
    oscillation u v mu mv =
     Close-from-interval ε (r ℚ- η) (r ℚ+ η) (ιₐ r) (ιₐ s)
      (ιₐ-lower (r ℚ- η) r (ℚ<-subtraction-preserves-order r η η-is-positive))
      (ιₐ-upper r (r ℚ+ η) (ℚ<-addition-preserves-order'' r η η-is-positive))
      (ιₐ-lower (r ℚ- η) s (pr₁ II))
      (ιₐ-upper s (r ℚ+ η) (pr₂ II))
      (widened-point r η ε (twice-a-quarter η ε l (ℚ≤-refl η)))
     where
      r s : ℚ
      r = reciprocal (u 𝟎)
      s = reciprocal (v 𝟎)

      I : abs (s ℚ- r) < η
      I = ℚ≤-<-trans (abs (s ℚ- r)) (abs (v 𝟎 ℚ- u 𝟎)) η
           (reciprocal-is-Lipschitz (v 𝟎) (u 𝟎))
           (interval-gives-close (a 𝟎) (b 𝟎) (v 𝟎) (u 𝟎) η
             (pr₁ (mv 𝟎)) (pr₂ (mv 𝟎)) (pr₁ (mu 𝟎)) (pr₂ (mu 𝟎)) (w 𝟎))

      II : (r ℚ- η < s) × (s < r ℚ+ η)
      II = abs-gives-ball s r η I

open with-small-oscillation reciprocals-vary-little
 using (extension ; extension-is-continuous ; extension-at-samples)

\end{code}

The reciprocal of max(1 , s), its agreement with the rational version,
and its continuity.

\begin{code}

reciprocal-ℝ : ℝ → ℝ
reciprocal-ℝ s = extension (λ _ → s)

reciprocal-ℝ-agrees : (q : ℚ) → reciprocal-ℝ (ιₐ q) ＝ ιₐ (reciprocal q)
reciprocal-ℝ-agrees q = extension-at-samples (λ _ → q)

reciprocal-ℝ-is-continuous
 : {m : ℕ} (A : (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
 → Coordinatewise-Strictly-Continuous A x
 → Coordinatewise-Strictly-Continuous (λ y → reciprocal-ℝ (A y)) x
reciprocal-ℝ-is-continuous A x cA =
 composition-is-continuous extension (λ _ y → A y) x
  (extension-is-continuous (λ _ → A x)) (λ _ → cA)

\end{code}

It is at most 1, by its value at rational points; and it is 1 where
s ≤ 1: if it were below some rational q < 1 at s, the rational points
of some interval (a , b) around s would have reciprocals below q, but
the interval has a rational point at most 1, whose reciprocal is 1.

\begin{code}

reciprocal-ℝ-≤-one : (s : ℝ) → reciprocal-ℝ s ≤ 1ℝ
reciprocal-ℝ-≤-one s =
 transport (reciprocal-ℝ s ≤_) {ιₐ 1ℚ} {1ℝ} (1ℝ-is-ιₐ ⁻¹)
  (≤-at-a-continuity-point F G t cF cG h)
 where
  t : Fin 1 → ℝ
  t _ = s

  F G : (Fin 1 → ℝ) → ℝ
  F v = reciprocal-ℝ (v 𝟎)
  G v = ιₐ 1ℚ

  cF : Coordinatewise-Strictly-Continuous F t
  cF = reciprocal-ℝ-is-continuous (λ v → v 𝟎) t (projection-is-continuous 𝟎 t)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = constant-is-continuous (ιₐ 1ℚ) t

  h : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i))
  h q = transport (_≤ ιₐ 1ℚ) {ιₐ (reciprocal (q 𝟎))} {reciprocal-ℝ (ιₐ (q 𝟎))}
         (reciprocal-ℝ-agrees (q 𝟎) ⁻¹)
         (ιₐ-≤-ιₐ (reciprocal (q 𝟎)) 1ℚ (reciprocal-≤-one (q 𝟎)))

reciprocal-ℝ-of-at-most-one : (s : ℝ) → s ≤ 1ℝ → reciprocal-ℝ s ＝ 1ℝ
reciprocal-ℝ-of-at-most-one s l =
 ℝ<-tight (reciprocal-ℝ s) 1ℝ not-below not-above
 where
  not-above : ¬ (1ℝ < reciprocal-ℝ s)
  not-above =
   ℝ-less-than-or-equal-not-greater (reciprocal-ℝ s) 1ℝ (reciprocal-ℝ-≤-one s)

  not-below : ¬ (reciprocal-ℝ s < 1ℝ)
  not-below k = ∥∥-rec 𝟘-is-prop γ k
   where
    γ : (Σ q ꞉ ℚ , (reciprocal-ℝ s < q) × (q < 1ℝ)) → 𝟘
    γ (q , a , b) = ∥∥-rec 𝟘-is-prop δ a
     where
      q<1 : q < 1ℚ
      q<1 = ιₐ-lower⁻¹ q 1ℚ (transport (q <_) {1ℝ} {ιₐ 1ℚ} 1ℝ-is-ιₐ b)

      δ : Above-Witness (λ _ → s) q → 𝟘
      δ ((a' , b' , q') , m , q'<q , upper) =
       ℚ<-irrefl q (ℚ<-trans q 1ℚ q q<1 1<q)
       where
        a'<1 : a' 𝟎 < 1ℚ
        a'<1 = ιₐ-lower⁻¹ (a' 𝟎) 1ℚ
                (transport (a' 𝟎 <_) {1ℝ} {ιₐ 1ℚ} 1ℝ-is-ιₐ
                  (<-≤-trans-ℚ s 1ℝ (a' 𝟎) (pr₁ (m 𝟎)) l))

        c : Σ c ꞉ ℚ , (a' 𝟎 < c) × (c < b' 𝟎) × (c ≤ 1ℚ)
        c = point-at-most-one (a' 𝟎) (b' 𝟎)
             (cuts-are-ordered s (a' 𝟎) (b' 𝟎) (pr₁ (m 𝟎)) (pr₂ (m 𝟎))) a'<1

        in-box : In-Box a' b' (λ _ → pr₁ c)
        in-box 𝟎       = pr₁ (pr₂ c) , pr₁ (pr₂ (pr₂ c))
        in-box (suc i) = 𝟘-elim i

        1<q' : 1ℚ < q'
        1<q' = ιₐ-upper⁻¹ 1ℚ q'
                (transport (λ - → ιₐ - < q') {reciprocal (pr₁ c)} {1ℚ}
                  (reciprocal-of-at-most-one (pr₁ c) (pr₂ (pr₂ (pr₂ c))))
                  (upper (λ _ → pr₁ c) in-box))

        1<q : 1ℚ < q
        1<q = ℚ<-trans 1ℚ q' q 1<q' q'<q

\end{code}

The bound used for the ball: s (1 / max(1 , s))² ≤ 1, by its value at
rational points.

\begin{code}

reciprocal-ℝ-bound : (s : ℝ) → s * (reciprocal-ℝ s * reciprocal-ℝ s) ≤ 1ℝ
reciprocal-ℝ-bound s =
 transport (s * (reciprocal-ℝ s * reciprocal-ℝ s) ≤_) {ιₐ 1ℚ} {1ℝ} (1ℝ-is-ιₐ ⁻¹)
  (≤-at-a-continuity-point F G t cF cG h)
 where
  t : Fin 1 → ℝ
  t _ = s

  F G : (Fin 1 → ℝ) → ℝ
  F v = v 𝟎 * (reciprocal-ℝ (v 𝟎) * reciprocal-ℝ (v 𝟎))
  G v = ιₐ 1ℚ

  p : Coordinatewise-Strictly-Continuous (λ v → v 𝟎) t
  p = projection-is-continuous 𝟎 t

  r : Coordinatewise-Strictly-Continuous (λ v → reciprocal-ℝ (v 𝟎)) t
  r = reciprocal-ℝ-is-continuous (λ v → v 𝟎) t p

  cF : Coordinatewise-Strictly-Continuous F t
  cF = product-is-continuous (λ v → v 𝟎)
        (λ v → reciprocal-ℝ (v 𝟎) * reciprocal-ℝ (v 𝟎)) t
        p (product-is-continuous (λ v → reciprocal-ℝ (v 𝟎))
            (λ v → reciprocal-ℝ (v 𝟎)) t r r)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = constant-is-continuous (ιₐ 1ℚ) t

  h : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i))
  h q = transport (_≤ ιₐ 1ℚ)
         {ιₐ (q 𝟎 ℚ* (reciprocal (q 𝟎) ℚ* reciprocal (q 𝟎)))}
         {ιₐ (q 𝟎) * (reciprocal-ℝ (ιₐ (q 𝟎)) * reciprocal-ℝ (ιₐ (q 𝟎)))}
         e
         (ιₐ-≤-ιₐ (q 𝟎 ℚ* (reciprocal (q 𝟎) ℚ* reciprocal (q 𝟎))) 1ℚ
           (reciprocal-bound (q 𝟎)))
   where
    e : ιₐ (q 𝟎 ℚ* (reciprocal (q 𝟎) ℚ* reciprocal (q 𝟎)))
      ＝ ιₐ (q 𝟎) * (reciprocal-ℝ (ιₐ (q 𝟎)) * reciprocal-ℝ (ιₐ (q 𝟎)))
    e = ιₐ-* (q 𝟎) (reciprocal (q 𝟎) ℚ* reciprocal (q 𝟎)) ⁻¹
      ∙ ap (ιₐ (q 𝟎) *_)
          (ιₐ-* (reciprocal (q 𝟎)) (reciprocal (q 𝟎)) ⁻¹
           ∙ ap₂ _*_ (reciprocal-ℝ-agrees (q 𝟎) ⁻¹)
              (reciprocal-ℝ-agrees (q 𝟎) ⁻¹))

\end{code}

The inverse of a positive real number A (gate G14, step E4). For a
rational c with 0 < c < A, put k = 1/c + 1/c. Then k A > 1, because
(1/c) c = 1 with 1/c < k and c < A (products-above); so
k A (1 / max(1 , k A)) = 1, and z = k (1 / max(1 , k A)) has z A = 1.
Inverses are unique, so the type of nonnegative inverses of A is a
proposition, and the merely existing c gives an element of it. The law
s (1 / max(1 , s)) = 1 for s > 1 holds at the rational points of an
interval around s above 1, and s (1 / max(1 , s)) ≤ 1 at all rational
points; so it follows from ≤-near-a-continuity-point and
≤-at-a-continuity-point. agda-unimath's module
real-numbers.multiplicative-inverses-positive-real-numbers defines the
inverse by cuts; we reuse 1 / max(1 , s) instead.

\begin{code}

times-reciprocal-ℝ-at-rationals
 : (r : ℚ) → ιₐ r * reciprocal-ℝ (ιₐ r) ＝ ιₐ (r ℚ* reciprocal r)
times-reciprocal-ℝ-at-rationals r =
 ap (ιₐ r *_) (reciprocal-ℝ-agrees r) ∙ ιₐ-* r (reciprocal r)

times-reciprocal-ℝ-is-continuous
 : (t : Fin 1 → ℝ)
 → Coordinatewise-Strictly-Continuous (λ v → v 𝟎 * reciprocal-ℝ (v 𝟎)) t
times-reciprocal-ℝ-is-continuous t =
 product-is-continuous (λ v → v 𝟎) (λ v → reciprocal-ℝ (v 𝟎)) t
  (projection-is-continuous 𝟎 t)
  (reciprocal-ℝ-is-continuous (λ v → v 𝟎) t (projection-is-continuous 𝟎 t))

times-reciprocal-ℝ-≤-one : (s : ℝ) → s * reciprocal-ℝ s ≤ 1ℝ
times-reciprocal-ℝ-≤-one s =
 transport (s * reciprocal-ℝ s ≤_) {ιₐ 1ℚ} {1ℝ} (1ℝ-is-ιₐ ⁻¹)
  (≤-at-a-continuity-point F G t (times-reciprocal-ℝ-is-continuous t)
    (constant-is-continuous (ιₐ 1ℚ) t) h)
 where
  t : Fin 1 → ℝ
  t _ = s

  F G : (Fin 1 → ℝ) → ℝ
  F v = v 𝟎 * reciprocal-ℝ (v 𝟎)
  G v = ιₐ 1ℚ

  h : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i))
  h q = transport (_≤ ιₐ 1ℚ) {ιₐ (q 𝟎 ℚ* reciprocal (q 𝟎))}
         {ιₐ (q 𝟎) * reciprocal-ℝ (ιₐ (q 𝟎))}
         (times-reciprocal-ℝ-at-rationals (q 𝟎) ⁻¹)
         (ιₐ-≤-ιₐ (q 𝟎 ℚ* reciprocal (q 𝟎)) 1ℚ (times-reciprocal-≤-one (q 𝟎)))

times-reciprocal-ℝ-above-one : (s : ℝ) → 1ℝ < s → s * reciprocal-ℝ s ＝ 1ℝ
times-reciprocal-ℝ-above-one s l =
 ℝ<-tight (s * reciprocal-ℝ s) 1ℝ not-below not-above
 where
  not-above : ¬ (1ℝ < s * reciprocal-ℝ s)
  not-above = ℝ-less-than-or-equal-not-greater (s * reciprocal-ℝ s) 1ℝ
               (times-reciprocal-ℝ-≤-one s)

  t : Fin 1 → ℝ
  t _ = s

  not-below : ¬ (s * reciprocal-ℝ s < 1ℝ)
  not-below m = ∥∥-rec 𝟘-is-prop γ (binary-choice l (inhabited-from-real-R s))
   where
    γ : (Σ c ꞉ ℚ , (1ℝ < c) × (c < s)) × (Σ b ꞉ ℚ , s < b) → 𝟘
    γ ((c , n , n') , (b , o)) =
     ℝ-less-than-or-equal-not-greater 1ℝ (s * reciprocal-ℝ s)
      (transport (_≤ s * reciprocal-ℝ s) {ιₐ 1ℚ} {1ℝ} (1ℝ-is-ιₐ ⁻¹) I) m
     where
      around : Around (λ _ → c) (λ _ → b) t
      around _ = n' , o

      h : (q : Fin 1 → ℚ) → In-Box (λ _ → c) (λ _ → b) q
        → ιₐ 1ℚ ≤ ιₐ (q 𝟎) * reciprocal-ℝ (ιₐ (q 𝟎))
      h q w = transport (ιₐ 1ℚ ≤_) {ιₐ 1ℚ} {ιₐ (q 𝟎) * reciprocal-ℝ (ιₐ (q 𝟎))}
               (ap ιₐ (times-reciprocal-of-at-least-one (q 𝟎) one-≤-q ⁻¹)
                ∙ times-reciprocal-ℝ-at-rationals (q 𝟎) ⁻¹)
               (ℝ≤-refl (ιₐ 1ℚ))
       where
        one-≤-q : 1ℚ ≤ q 𝟎
        one-≤-q = ℚ<-coarser-than-≤ 1ℚ (q 𝟎) (ℚ<-trans 1ℚ c (q 𝟎) n (pr₁ (w 𝟎)))

      I : ιₐ 1ℚ ≤ s * reciprocal-ℝ s
      I = ≤-near-a-continuity-point (λ _ → ιₐ 1ℚ)
           (λ v → v 𝟎 * reciprocal-ℝ (v 𝟎)) t
           (λ _ → c) (λ _ → b) around (constant-is-continuous (ιₐ 1ℚ) t)
           (times-reciprocal-ℝ-is-continuous t) h

scaled-reciprocal-ℝ-is-nonneg : (k : ℚ) → 0ℚ ≤ k → (s : ℝ)
                              → 0ℝ ≤ ιₐ k * reciprocal-ℝ s
scaled-reciprocal-ℝ-is-nonneg k l s =
 transport (_≤ ιₐ k * reciprocal-ℝ s) {ιₐ 0ℚ} {0ℝ} (0ℝ-is-ιₐ ⁻¹)
  (≤-at-a-continuity-point F G t (constant-is-continuous (ιₐ 0ℚ) t) cG h)
 where
  t : Fin 1 → ℝ
  t _ = s

  F G : (Fin 1 → ℝ) → ℝ
  F v = ιₐ 0ℚ
  G v = ιₐ k * reciprocal-ℝ (v 𝟎)

  cG : Coordinatewise-Strictly-Continuous G t
  cG = product-is-continuous (λ _ → ιₐ k) (λ v → reciprocal-ℝ (v 𝟎)) t
        (constant-is-continuous (ιₐ k) t)
        (reciprocal-ℝ-is-continuous (λ v → v 𝟎) t
          (projection-is-continuous 𝟎 t))

  h : (q : Fin 1 → ℚ) → F (λ i → ιₐ (q i)) ≤ G (λ i → ιₐ (q i))
  h q = transport (ιₐ 0ℚ ≤_) {ιₐ (k ℚ* reciprocal (q 𝟎))}
         {ιₐ k * reciprocal-ℝ (ιₐ (q 𝟎))}
         ((ap (ιₐ k *_) (reciprocal-ℝ-agrees (q 𝟎)) ∙ ιₐ-* k (reciprocal (q 𝟎)))
           ⁻¹)
         (ιₐ-≤-ιₐ 0ℚ (k ℚ* reciprocal (q 𝟎))
           (ℚ≤-pos-multiplication-preserves-order k (reciprocal (q 𝟎)) l
             (reciprocal-is-nonneg (q 𝟎))))

Inverse : ℝ → 𝓤₁ ̇
Inverse A = Σ z ꞉ ℝ , (z * A ＝ 1ℝ) × (0ℝ ≤ z)

inverses-are-unique : (A : ℝ) → is-prop (Inverse A)
inverses-are-unique A (z , e , _) (z' , e' , _) =
 to-subtype-＝ (λ y → ×-is-prop ℝ-is-set (≤-is-prop 0ℝ y)) I
 where
  I : z ＝ z'
  I = z            ＝⟨ *-right-unit z ⁻¹ ⟩
      z * 1ℝ       ＝⟨ ap (z *_) (e' ⁻¹) ⟩
      z * (z' * A) ＝⟨ ap (z *_) (*-comm z' A) ⟩
      z * (A * z') ＝⟨ *-assoc z A z' ⁻¹ ⟩
      (z * A) * z' ＝⟨ ap (_* z') e ⟩
      1ℝ * z'      ＝⟨ *-left-unit z' ⟩
      z'           ∎

inverse-of-positive : (A : ℝ) → 0ℝ < A → Inverse A
inverse-of-positive A l = ∥∥-rec (inverses-are-unique A) γ l
 where
  γ : (Σ c ꞉ ℚ , (0ℝ < c) × (c < A)) → Inverse A
  γ (c , m , n) = z , z-law ,
   scaled-reciprocal-ℝ-is-nonneg k (ℚ<-coarser-than-≤ 0ℚ k k-is-positive) s
   where
    c-is-positive : 0ℚ < c
    c-is-positive = 0ℝ-below-positive⁻¹ c m

    c-is-not-zero : ¬ (c ＝ 0ℚ)
    c-is-not-zero = ℚ<-positive-not-zero c c-is-positive

    c⁻¹ : ℚ
    c⁻¹ = ℚ*-inv c c-is-not-zero

    c⁻¹-is-positive : 0ℚ < c⁻¹
    c⁻¹-is-positive = ℚ-inv-preserves-pos c c-is-positive c-is-not-zero

    k : ℚ
    k = c⁻¹ ℚ+ c⁻¹

    c⁻¹<k : c⁻¹ < k
    c⁻¹<k = ℚ<-addition-preserves-order'' c⁻¹ c⁻¹ c⁻¹-is-positive

    k-is-positive : 0ℚ < k
    k-is-positive = ℚ<-trans 0ℚ c⁻¹ k c⁻¹-is-positive c⁻¹<k

    s : ℝ
    s = ιₐ k * A

    one-below : 1ℚ < s
    one-below = transport (_< s) {c⁻¹ ℚ* c} {1ℚ}
                 (ℚ*-comm c⁻¹ c ∙ ℚ*-inverse-product c c-is-not-zero)
                 (products-above c⁻¹ c (ιₐ k) A c⁻¹-is-positive c-is-positive
                   (ιₐ-lower c⁻¹ k c⁻¹<k) n)

    one-below-s : 1ℝ < s
    one-below-s =
     ∥∥-functor (λ (q , o , o') → q , o , o') (rounded-left-d s 1ℚ one-below)

    r : ℝ
    r = reciprocal-ℝ s

    z : ℝ
    z = ιₐ k * r

    z-law : z * A ＝ 1ℝ
    z-law = (ιₐ k * r) * A ＝⟨ *-assoc (ιₐ k) r A ⟩
            ιₐ k * (r * A) ＝⟨ ap (ιₐ k *_) (*-comm r A) ⟩
            ιₐ k * (A * r) ＝⟨ *-assoc (ιₐ k) A r ⁻¹ ⟩
            s * r          ＝⟨ times-reciprocal-ℝ-above-one s one-below-s ⟩
            1ℝ             ∎

inverse : (A : ℝ) → 0ℝ < A → ℝ
inverse A l = pr₁ (inverse-of-positive A l)

inverse-law : (A : ℝ) (l : 0ℝ < A) → inverse A l * A ＝ 1ℝ
inverse-law A l = pr₁ (pr₂ (inverse-of-positive A l))

inverse-is-nonneg : (A : ℝ) (l : 0ℝ < A) → 0ℝ ≤ inverse A l
inverse-is-nonneg A l = pr₂ (pr₂ (inverse-of-positive A l))

\end{code}
