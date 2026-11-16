Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The extension of a 1-Lipschitz rational function to the reals.

A 1-Lipschitz function f : ℚ → ℚ is uniformly continuous, with modulus
δ ε = ε, so the extension theorem of DedekindReals.Extension gives a
function on ℝ that agrees with f on the rationals. Its cuts are
described in terms of rational balls: p is below the value at x if
x lies in a ball (x₀ - ε , x₀ + ε) with p < f x₀ - ε. We derive the
facts used for concrete functions:

 * a lower bound m for f on a rational interval (a , b) gives
   p < value at x for every real x in (a , b) and every p < m, and
   similarly for upper bounds;

 * if f is 0 on [lo , hi], then so is the extension, at all real
   points of [lo , hi].

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.LipschitzExtension
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.MinMax
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Positive hiding (_+_ ; _*_)
open import Rationals.Type
open import UF.Base
open import UF.Powerset
open import DedekindReals.Extension fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.RationalArithmetic
open import gist.RealCohesion.RationalLipschitz
open import gist.RealCohesion.RealOrder fe pe pt

open PropositionalTruncation pt

\end{code}

The extension.

\begin{code}

Lipschitz-gives-uc : (f : ℚ → ℚ) → Lipschitz f → ℚ-is-uniformly-continuous f
Lipschitz-gives-uc f l (ε , 0<ε) = (ε , 0<ε) , γ
 where
  γ : (x x₀ : ℚ) → x ∈𝐁 (ε , 0<ε) ⦅ x₀ ⦆ → f x ∈𝐁 (ε , 0<ε) ⦅ f x₀ ⦆
  γ x x₀ (a , b) = abs-gives-ball (f x) (f x₀) ε
                    (ℚ≤-<-trans (abs (f x - f x₀)) (abs (x - x₀)) ε
                      (l x x₀) (ball-gives-abs x x₀ ε a b))

extension : (f : ℚ → ℚ) → Lipschitz f → ℝ → ℝ
extension f l = extend f (Lipschitz-gives-uc f l)

extension-agrees : (f : ℚ → ℚ) (l : Lipschitz f) (q : ℚ)
                 → extension f l (ι q) ＝ ι (f q)
extension-agrees f l = extend-is-extension f (Lipschitz-gives-uc f l)

\end{code}

Bounds.

\begin{code}

module _ (f : ℚ → ℚ) (l : Lipschitz f) where

 private
  uc : ℚ-is-uniformly-continuous f
  uc = Lipschitz-gives-uc f l

  E : ℝ → ℝ
  E = extension f l

  Shrunk-Ball : (x : ℝ) (a b c : ℚ) → 𝓤₀ ̇
  Shrunk-Ball x a b c = Σ (x₀ , ε) ꞉ ℚ × ℚ , (0ℚ < ε) × (ε < c)
                                          × (x₀ - ε < x) × (x < x₀ + ε)
                                          × (a < x₀) × (x₀ < b)

 below-extension : (x : ℝ) (x₀ ε p : ℚ) (0<ε : 0ℚ < ε)
                 → x₀ - ε < x → x < x₀ + ε → p < f x₀ - ε → p < E x
 below-extension x x₀ ε p 0<ε a b c = ∣ (x₀ , ε , 0<ε) , (a , b) , c ∣

 above-extension : (x : ℝ) (x₀ ε q : ℚ) (0<ε : 0ℚ < ε)
                 → x₀ - ε < x → x < x₀ + ε → f x₀ + ε < q → E x < q
 above-extension x x₀ ε q 0<ε a b c = ∣ (x₀ , ε , 0<ε) , (a , b) , c ∣

 private
  shrunk-ball : (x : ℝ) (a b c : ℚ) → a < x → x < b → 0ℚ < c
              → ∥ Shrunk-Ball x a b c ∥
  shrunk-ball x a b c a<x x<b 0<c = ∥∥-rec ∥∥-is-prop γ (rounded-left-d x a a<x)
   where
    γ : (Σ a' ꞉ ℚ , a < a' < x) → ∥ Shrunk-Ball x a b c ∥
    γ (a' , a<a' , a'<x) = ∥∥-rec ∥∥-is-prop δ
                            (rounded-right-b (upper-cut-of x)
                              (rounded-from-real-R x) b x<b)
     where
      δ : (Σ b' ꞉ ℚ , (b' < b) × (x < b')) → ∥ Shrunk-Ball x a b c ∥
      δ (b' , b'<b , x<b') = ∥∥-functor ζ (ball-around-real x (ε , 0<ε) f uc)
       where
        μ : ℚ
        μ = min c (min (a' - a) (b - b'))

        0<μ : 0ℚ < μ
        0<μ = min-is-positive c (min (a' - a) (b - b')) 0<c
               (min-is-positive (a' - a) (b - b')
                 (ℚ<-difference-positive a a' a<a')
                 (ℚ<-difference-positive b' b b'<b))

        ε : ℚ
        ε = half μ

        0<ε : 0ℚ < ε
        0<ε = half-is-positive μ 0<μ

        ε≤μ : ε ≤ μ
        ε≤μ = ℚ<-coarser-than-≤ ε μ (half-is-less μ 0<μ)

        ε<c : ε < c
        ε<c =
         ℚ<-≤-trans ε μ c (half-is-less μ 0<μ) (min≤ c (min (a' - a) (b - b')))

        μ≤a'-a : μ ≤ a' - a
        μ≤a'-a = ℚ≤-trans μ (min (a' - a) (b - b')) (a' - a)
                  (min≤' c (min (a' - a) (b - b'))) (min≤ (a' - a) (b - b'))

        μ≤b-b' : μ ≤ b - b'
        μ≤b-b' = ℚ≤-trans μ (min (a' - a) (b - b')) (b - b')
                  (min≤' c (min (a' - a) (b - b'))) (min≤' (a' - a) (b - b'))

        ζ : (Σ x₀ ꞉ ℚ , x ℝ∈𝐁 δ⦅⦆ f uc (ε , 0<ε) ⦅ x₀ ⦆) → Shrunk-Ball x a b c
        ζ (x₀ , (d , e)) = (x₀ , ε) , 0<ε , ε<c , d , e , a<x₀ , x₀<b
         where
          a'<x₀+ε : a' < x₀ + ε
          a'<x₀+ε = cuts-are-ordered x a' (x₀ + ε) a'<x e

          a≤a'-ε : a ≤ a' - ε
          a≤a'-ε = ≤-sub-right a a' ε
                    (transport (_≤ a') (ℚ+-comm ε a)
                      (≤-add-right ε a' a (ℚ≤-trans ε μ (a' - a) ε≤μ μ≤a'-a)))

          a<x₀ : a < x₀
          a<x₀ = ℚ≤-<-trans a (a' - ε) x₀ a≤a'-ε (<-move-left a' x₀ ε a'<x₀+ε)

          b'+ε≤b : b' + ε ≤ b
          b'+ε≤b = transport (_≤ b) (ℚ+-comm ε b')
                    (≤-add-right ε b b' (ℚ≤-trans ε μ (b - b') ε≤μ μ≤b-b'))

          x₀<b : x₀ < b
          x₀<b = ℚ<-≤-trans x₀ (b' + ε) b
                  (<-move-right x₀ b' ε (cuts-are-ordered x (x₀ - ε) b' d x<b'))
                  b'+ε≤b

 lower-bound-transfer : (a b m : ℚ)
                      → ((y : ℚ) → a < y → y < b → m ≤ f y)
                      → (x : ℝ) → a < x → x < b → (p : ℚ) → p < m → p < E x
 lower-bound-transfer a b m bound x a<x x<b p p<m =
  ∥∥-rec (∈-is-prop (lower-cut-of (E x)) p) γ
   (shrunk-ball x a b (m - p) a<x x<b (ℚ<-difference-positive p m p<m))
  where
   γ : Shrunk-Ball x a b (m - p) → p < E x
   γ ((x₀ , ε) , 0<ε , ε<m-p , d , e , a<x₀ , x₀<b) =
    below-extension x x₀ ε p 0<ε d e
     (<-sub-right p (f x₀) ε
       (ℚ<-≤-trans (p + ε) m (f x₀)
         (transport (_< m) (ℚ+-comm ε p) (<-add-right ε m p ε<m-p))
         (bound x₀ a<x₀ x₀<b)))

 upper-bound-transfer : (a b M : ℚ)
                      → ((y : ℚ) → a < y → y < b → f y ≤ M)
                      → (x : ℝ) → a < x → x < b → (q : ℚ) → M < q → E x < q
 upper-bound-transfer a b M bound x a<x x<b q M<q =
  ∥∥-rec (∈-is-prop (upper-cut-of (E x)) q) γ
   (shrunk-ball x a b (q - M) a<x x<b (ℚ<-difference-positive M q M<q))
  where
   γ : Shrunk-Ball x a b (q - M) → E x < q
   γ ((x₀ , ε) , 0<ε , ε<q-M , d , e , a<x₀ , x₀<b) =
    above-extension x x₀ ε q 0<ε d e
     (ℚ≤-<-trans (f x₀ + ε) (M + ε) q
       (ℚ≤-addition-preserves-order (f x₀) M ε (bound x₀ a<x₀ x₀<b))
       (transport (_< q) (ℚ+-comm ε M) (<-add-right ε q M ε<q-M)))

\end{code}

Flatness.

\begin{code}

 flat-transfer : (lo hi : ℚ) → lo ≤ hi
               → ((y : ℚ) → lo ≤ y → y ≤ hi → f y ＝ 0ℚ)
               → (x : ℝ) → ¬ (x < lo) → ¬ (hi < x) → E x ＝ 0ℝ
 flat-transfer lo hi lo≤hi flat x m m' =
  no-sign-gives-zero (E x) not-positive not-negative
  where
   small : (μ : ℚ) → 0ℚ < μ → (y : ℚ) → lo - μ < y → y < hi + μ → abs (f y) ≤ μ
   small μ 0<μ y a b = γ (ℚ-dichotomous' y lo)
    where
     through : (z : ℚ) → f z ＝ 0ℚ → abs (y - z) ≤ μ → abs (f y) ≤ μ
     through z e k = ℚ≤-trans (abs (f y)) (abs (y - z)) μ
                      (transport (λ w → abs w ≤ abs (y - z))
                        (ap (λ w → f y - w) e ∙ minus-zero (f y)) (l y z))
                      k

     lo-y<μ : lo - y < μ
     lo-y<μ = <-move-left lo μ y
               (transport (lo <_) (ℚ+-comm y μ) (<-move-right lo y μ a))

     y-hi<μ : y - hi < μ
     y-hi<μ = <-move-left y μ hi (transport (y <_) (ℚ+-comm hi μ) b)

     γ : (y < lo) ∔ (lo ≤ y) → abs (f y) ≤ μ
     γ (inl k) = through lo (flat lo (ℚ≤-refl lo) lo≤hi)
                  (transport (_≤ μ)
                    (ℚ≤-to-abs' y lo (ℚ<-coarser-than-≤ y lo k) ⁻¹)
                    (ℚ<-coarser-than-≤ (lo - y) μ lo-y<μ))
     γ (inr k) = δ (ℚ-dichotomous' hi y)
      where
       δ : (hi < y) ∔ (y ≤ hi) → abs (f y) ≤ μ
       δ (inl n) = through hi (flat hi lo≤hi (ℚ≤-refl hi))
                    (transport (_≤ μ)
                      ((abs-comm y hi
                        ∙ ℚ≤-to-abs' hi y (ℚ<-coarser-than-≤ hi y n)) ⁻¹)
                      (ℚ<-coarser-than-≤ (y - hi) μ y-hi<μ))
       δ (inr n) = transport (_≤ μ) (ℚ-abs-zero ∙ ap abs (flat y k n ⁻¹))
                    (ℚ<-coarser-than-≤ 0ℚ μ 0<μ)

   lower : (μ : ℚ) → 0ℚ < μ → (y : ℚ) → lo - μ < y → y < hi + μ → - μ ≤ f y
   lower μ 0<μ y a b = pr₁ (ℚ-abs-≤-unpack (f y) μ (small μ 0<μ y a b))

   upper : (μ : ℚ) → 0ℚ < μ → (y : ℚ) → lo - μ < y → y < hi + μ → f y ≤ μ
   upper μ 0<μ y a b = pr₂ (ℚ-abs-≤-unpack (f y) μ (small μ 0<μ y a b))

   left-end : (μ : ℚ) → 0ℚ < μ → lo - μ < x
   left-end μ 0<μ =
    located-above x (lo - μ) lo (ℚ<-subtraction-preserves-order lo μ 0<μ) m

   right-end : (μ : ℚ) → 0ℚ < μ → x < hi + μ
   right-end μ 0<μ =
    located-below x hi (hi + μ) (ℚ<-addition-preserves-order'' hi μ 0<μ) m'

   not-positive : ¬ (0ℚ < E x)
   not-positive k = ∥∥-rec 𝟘-is-prop γ (rounded-left-d (E x) 0ℚ k)
    where
     γ : (Σ e ꞉ ℚ , (0ℚ < e) × (e < E x)) → 𝟘
     γ (e , 0<e , e<Ex) = not-below-and-above (E x) e e<Ex
                           (upper-bound-transfer (lo - μ) (hi + μ) μ
                             (upper μ 0<μ) x
                             (left-end μ 0<μ) (right-end μ 0<μ) e
                              (half-is-less e 0<e))
      where
       μ : ℚ
       μ = half e

       0<μ : 0ℚ < μ
       0<μ = half-is-positive e 0<e

   not-negative : ¬ (E x < 0ℚ)
   not-negative k = ∥∥-rec 𝟘-is-prop γ
                     (rounded-right-b (upper-cut-of (E x))
                       (rounded-from-real-R (E x)) 0ℚ k)
    where
     γ : (Σ e ꞉ ℚ , (e < 0ℚ) × (E x < e)) → 𝟘
     γ (e , e<0 , Ex<e) = not-below-and-above (E x) e
                           (lower-bound-transfer (lo - μ) (hi + μ) (- μ)
                             (lower μ 0<μ) x
                             (left-end μ 0<μ) (right-end μ 0<μ) e e<-μ)
                           Ex<e
      where
       0<-e : 0ℚ < - e
       0<-e = ℚ<-swap'' e e<0

       μ : ℚ
       μ = half (- e)

       0<μ : 0ℚ < μ
       0<μ = half-is-positive (- e) 0<-e

       e<-μ : e < - μ
       e<-μ = transport (_< - μ) (ℚ-minus-minus e ⁻¹)
               (ℚ<-swap μ (- e) (half-is-less (- e) 0<-e))

\end{code}

Signs on rational intervals. If a signed version of f is bounded below
by a positive rational on (a , b), the extension has that sign on
(a , b). We apply this to functions that are linear, or tent-shaped, on
a rational interval.

\begin{code}

 signed-transfer : (σ : 𝟚) (a b m : ℚ) → 0ℚ < m
                 → ((y : ℚ) → a < y → y < b → m ≤ signed σ (f y))
                 → (x : ℝ) → a < x → x < b → Has-Sign σ (E x)
 signed-transfer ₁ a b m 0<m bound x a<x x<b =
  lower-bound-transfer a b m bound x a<x x<b 0ℚ 0<m
 signed-transfer ₀ a b m 0<m bound x a<x x<b =
  upper-bound-transfer a b (- m) bound' x a<x x<b 0ℚ
   (neg-is-negative m 0<m)
  where
   bound' : (y : ℚ) → a < y → y < b → f y ≤ - m
   bound' y c d = transport (_≤ - m) (ℚ-minus-minus (f y) ⁻¹)
                   (ℚ≤-swap m (- f y) (bound y c d))

 private
  signed-bound : (σ : 𝟚) (y v m : ℚ) → f y ＝ signed σ v → m ≤ v
               → m ≤ signed σ (f y)
  signed-bound σ y v m e l = transport (m ≤_)
                              (signed-involutive σ v ⁻¹ ∙ ap (signed σ) (e ⁻¹))
                               l

 increasing-signed : (σ : 𝟚) (u v : ℚ)
                   → ((y : ℚ) → u ≤ y → y ≤ v → f y ＝ signed σ (y - u))
                   → (x : ℝ) → u < x → x < v → Has-Sign σ (E x)
 increasing-signed σ u v formula x u<x x<v = ∥∥-rec (Has-Sign-is-prop σ (E x)) γ
                                              (rounded-left-d x u u<x)
  where
   γ : (Σ d ꞉ ℚ , u < d < x) → Has-Sign σ (E x)
   γ (d , u<d , d<x) =
    signed-transfer σ d v (d - u) (ℚ<-difference-positive u d u<d) bound x d<x
     x<v
    where
     bound : (y : ℚ) → d < y → y < v → d - u ≤ signed σ (f y)
     bound y d<y y<v = signed-bound σ y (y - u) (d - u)
                        (formula y
                          (ℚ<-coarser-than-≤ u y (ℚ<-trans u d y u<d d<y))
                                   (ℚ<-coarser-than-≤ y v y<v))
                        (ℚ≤-addition-preserves-order d y (- u)
                          (ℚ<-coarser-than-≤ d y d<y))

 decreasing-signed : (σ : 𝟚) (u v : ℚ)
                   → ((y : ℚ) → u ≤ y → y ≤ v → f y ＝ signed σ (v - y))
                   → (x : ℝ) → u < x → x < v → Has-Sign σ (E x)
 decreasing-signed σ u v formula x u<x x<v =
  ∥∥-rec (Has-Sign-is-prop σ (E x)) γ
   (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) v x<v)
  where
   γ : (Σ d ꞉ ℚ , (d < v) × (x < d)) → Has-Sign σ (E x)
   γ (d , d<v , x<d) =
    signed-transfer σ u d (v - d) (ℚ<-difference-positive d v d<v) bound x u<x
     x<d
    where
     bound : (y : ℚ) → u < y → y < d → v - d ≤ signed σ (f y)
     bound y u<y y<d = signed-bound σ y (v - y) (v - d)
                        (formula y (ℚ<-coarser-than-≤ u y u<y)
                                   (ℚ<-coarser-than-≤ y v
                                     (ℚ<-trans y d v y<d d<v)))
                        (ℚ≤-addition-preserves-order-left (- d) (- y) v
                          (ℚ≤-swap y d (ℚ<-coarser-than-≤ y d y<d)))

 tent-signed : (σ : 𝟚) (u w v : ℚ)
             → ((y : ℚ) → u ≤ y → y ≤ w → f y ＝ signed σ (y - u))
             → ((y : ℚ) → w ≤ y → y ≤ v → f y ＝ signed σ (v - y))
             → (x : ℝ) → u < x → x < v → Has-Sign σ (E x)
 tent-signed σ u w v rising falling x u<x x<v =
  ∥∥-rec (Has-Sign-is-prop σ (E x)) γ (rounded-left-d x u u<x)
  where
   γ : (Σ d ꞉ ℚ , u < d < x) → Has-Sign σ (E x)
   γ (d , u<d , d<x) =
    ∥∥-rec (Has-Sign-is-prop σ (E x)) δ
     (rounded-right-b (upper-cut-of x) (rounded-from-real-R x) v x<v)
    where
     δ : (Σ d' ꞉ ℚ , (d' < v) × (x < d')) → Has-Sign σ (E x)
     δ (d' , d'<v , x<d') = signed-transfer σ d d' m 0<m bound x d<x x<d'
      where
       m : ℚ
       m = min (d - u) (v - d')

       0<m : 0ℚ < m
       0<m = min-is-positive (d - u) (v - d')
              (ℚ<-difference-positive u d u<d)
               (ℚ<-difference-positive d' v d'<v)

       bound : (y : ℚ) → d < y → y < d' → m ≤ signed σ (f y)
       bound y d<y y<d' = ε (ℚ-dichotomous y w)
        where
         u≤y : u ≤ y
         u≤y = ℚ<-coarser-than-≤ u y (ℚ<-trans u d y u<d d<y)

         y≤v : y ≤ v
         y≤v = ℚ<-coarser-than-≤ y v (ℚ<-trans y d' v y<d' d'<v)

         ε : (y ≤ w) ∔ (w ≤ y) → m ≤ signed σ (f y)
         ε (inl k) = signed-bound σ y (y - u) m (rising y u≤y k)
                      (ℚ≤-trans m (d - u) (y - u) (min≤ (d - u) (v - d'))
                        (ℚ≤-addition-preserves-order d y (- u)
                          (ℚ<-coarser-than-≤ d y d<y)))
         ε (inr k) = signed-bound σ y (v - y) m (falling y k y≤v)
                      (ℚ≤-trans m (v - d') (v - y) (min≤' (d - u) (v - d'))
                        (ℚ≤-addition-preserves-order-left (- d') (- y) v
                          (ℚ≤-swap y d' (ℚ<-coarser-than-≤ y d' y<d'))))

\end{code}
