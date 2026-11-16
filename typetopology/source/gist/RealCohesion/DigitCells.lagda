Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Cells around 1/3 and 2/3, and codes near the centre, for gate G24 of
Claude Fable 5.2's second addendum: the third part of the curve of
Lemma 7.16 of the write-up, in the form of
gist.RealCohesion.DigitCodes.

The cell of level k around c is the open interval of radius 2⁻ᵏ/3
around c. Its points have the binary digits of c for k places: for
c = 1/3 they are 0, 1, 0, 1, …, and for c = 2/3 they are 1, 0, 1, 0, ….
Astra uses the dyadic cells (b_k, b_k + 2⁻ᵏ) around 1/3, which contain
these intervals; the intervals need no floor function, and suffice,
because the proof needs a neighbourhood of the centre on which the
first k digits are fixed.

So if the coordinates w i of a rational vector lie in the cells of
level k around 1/3 and 2/3, alternately, then the first k blocks of the
code of w at any level K ≥ k agree with those of the centre 1/4, and
the code is within 2⁻ᵏ of 1/4.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.DigitCells where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import MLTT.Two-Properties using (complement)
open import Fin.Type using (Fin ; 𝟎 ; suc)
open import UF.Base using (ap₂ ; transport₂)
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Multiplication
open import gist.RealCohesion.RationalArithmetic
 using (half ; halves-add-up ; half-is-at-most ; minus-zero ; minus-plus)
open import gist.RealCohesion.DigitCodes

\end{code}

Radii and cells.

\begin{code}

radius : ℕ → ℚ
radius k = third (pow½ k)

centre-of : 𝟚 → ℚ
centre-of ₀ = 1/3
centre-of ₁ = 2/3

cell : ℕ → 𝟚 → ℚ → 𝓤₀ ̇
cell k b s = (centre-of b - radius k < s) × (s < centre-of b + radius k)

radius-halves : (k : ℕ) → radius (succ k) + radius (succ k) ＝ radius k
radius-halves k = ℚ-distributivity' 1/3 (pow½ (succ k)) (pow½ (succ k)) ⁻¹
                ∙ ap third
                   (ap (λ x → x + x) (pow½-succ k) ∙ halves-add-up (pow½ k))

pow½-at-most-one : (k : ℕ) → pow½ k ≤ 1ℚ
pow½-at-most-one 0        = ℚ≤-refl 1ℚ
pow½-at-most-one (succ k) = transport (_≤ 1ℚ) (pow½-succ k ⁻¹)
                             (ℚ≤-trans (half (pow½ k)) (pow½ k) 1ℚ
                               (half-is-at-most (pow½ k) (pow½-is-nonneg k))
                               (pow½-at-most-one k))

pow½-succ-at-most-half : (k : ℕ) → pow½ (succ k) ≤ 1/2
pow½-succ-at-most-half k = transport (_≤ 1/2) (pow½-succ k ⁻¹)
                            (transport (half (pow½ k) ≤_) (ℚ-mult-left-id 1/2)
                              (ℚ≤-pos-multiplication-preserves-order' (pow½ k)
                                1ℚ 1/2
                                (pow½-at-most-one k)
                                 (ℚ<-coarser-than-≤ 0ℚ 1/2 0<1/2)))

pow½-is-positive : (k : ℕ) → 0ℚ < pow½ k
pow½-is-positive 0        = 0<1
pow½-is-positive (succ k) = transport (0ℚ <_) (pow½-succ k ⁻¹)
                             (ℚ<-pos-multiplication-preserves-order (pow½ k) 1/2
                               (pow½-is-positive k) 0<1/2)

radius-is-positive : (k : ℕ) → 0ℚ < radius k
radius-is-positive k = ℚ<-pos-multiplication-preserves-order (pow½ k) 1/3
                        (pow½-is-positive k) 0<1/3

abstract
 1/3+third-of-half : 1/3 + third 1/2 ＝ 1/2
 1/3+third-of-half = refl

 2/3-third-of-half : 2/3 - third 1/2 ＝ 1/2
 2/3-third-of-half = refl

 2/3+2/3-1 : (2/3 + 2/3) - 1ℚ ＝ 1/3
 2/3+2/3-1 = refl

 1/3-1/3 : 1/3 - 1/3 ＝ 0ℚ
 1/3-1/3 = refl

 2/3-1/3 : 2/3 - 1/3 ＝ 1/3
 2/3-1/3 = refl

 1/3+1/3'' : 1/3 + 1/3 ＝ 2/3
 1/3+1/3'' = refl

 2/3+1/3'' : 2/3 + 1/3 ＝ 1ℚ
 2/3+1/3'' = refl

 2/3<1 : 2/3 < 1ℚ
 2/3<1 = 0 , refl

 0<1/3' : 0ℚ < 1/3
 0<1/3' = 0<1/3

radius-small : (k : ℕ) → radius (succ k) ≤ third 1/2
radius-small k =
 third-is-monotone (pow½ (succ k)) 1/2 (pow½-succ-at-most-half k)

radius-at-most-third : (k : ℕ) → radius k ≤ 1/3
radius-at-most-third k = transport (radius k ≤_) third-of-one'
                          (third-is-monotone (pow½ k) 1ℚ (pow½-at-most-one k))
 where
  third-of-one' : third 1ℚ ＝ 1/3
  third-of-one' = ℚ-mult-left-id 1/3

\end{code}

Doubling the bounds of a cell.

\begin{code}

double-lower : (a r : ℚ) → (a - r) + (a - r) ＝ (a + a) - (r + r)
double-lower a r =
 interchange a (- r) a (- r) ∙ ap ((a + a) +_) (ℚ-minus-dist r r)

double-upper : (a r : ℚ) → (a + r) + (a + r) ＝ (a + a) + (r + r)
double-upper a r = interchange a r a r

minus-one-later : (x y : ℚ) → (x - y) - 1ℚ ＝ (x - 1ℚ) - y
minus-one-later x y = ℚ+-rearrange x (- y) (- 1ℚ)

plus-minus-one-later : (x y : ℚ) → (x + y) - 1ℚ ＝ (x - 1ℚ) + y
plus-minus-one-later x y = ℚ+-rearrange x y (- 1ℚ)

\end{code}

The reading of a cell: a point of the cell of level k + 1 around
centre-of b has first digit b, and T sends it into the cell of level k
around the other centre, centre-of (complement b).

\begin{code}

cell-reading : (k : ℕ) (b : 𝟚) (s : ℚ) → cell (succ k) b s
             → (β s ＝ b) × cell k (complement b) (T s)
cell-reading k ₀ s (l , m) =
 β₀ , transport (λ c → cell k ₁ ((s + s) - bit c)) (β₀ ⁻¹)
                                   (transport (cell k ₁) (minus-zero (s + s) ⁻¹)
                                     (lower , upper))
 where
  r : ℚ
  r = radius (succ k)

  β₀ : β s ＝ ₀
  β₀ = β-small s (ℚ<-≤-trans s (1/3 + r) 1/2 m
                   (transport (1/3 + r ≤_) 1/3+third-of-half
                     (ℚ≤-adding 1/3 1/3 r (third 1/2) (ℚ≤-refl 1/3)
                       (radius-small k))))

  lower : 2/3 - radius k < s + s
  lower = transport (_< s + s)
           (double-lower 1/3 r
            ∙ ap₂ (λ x y → x - y) 1/3+1/3'' (radius-halves k))
           (ℚ<-adding (1/3 - r) s (1/3 - r) s l l)

  upper : s + s < 2/3 + radius k
  upper = transport (s + s <_)
           (double-upper 1/3 r ∙ ap₂ _+_ 1/3+1/3'' (radius-halves k))
           (ℚ<-adding s (1/3 + r) s (1/3 + r) m m)
cell-reading k ₁ s (l , m) =
 β₁ , transport (λ c → cell k ₀ ((s + s) - bit c)) (β₁ ⁻¹)
                                   (lower , upper)
 where
  r : ℚ
  r = radius (succ k)

  β₁ : β s ＝ ₁
  β₁ = β-large s (ℚ<-coarser-than-≤ 1/2 s
                   (ℚ≤-<-trans 1/2 (2/3 - r) s
                     (transport (_≤ 2/3 - r) 2/3-third-of-half
                       (ℚ≤-adding 2/3 2/3 (- third 1/2) (- r) (ℚ≤-refl 2/3)
                         (ℚ≤-swap r (third 1/2) (radius-small k))))
                     l))

  lower : 1/3 - radius k < (s + s) - 1ℚ
  lower = transport (_< (s + s) - 1ℚ)
           (ap (_- 1ℚ)
             (double-lower 2/3 r ∙ ap (λ x → (2/3 + 2/3) - x) (radius-halves k))
            ∙ minus-one-later (2/3 + 2/3) (radius k)
            ∙ ap (_- radius k) 2/3+2/3-1)
           (ℚ<-addition-preserves-order ((2/3 - r) + (2/3 - r)) (s + s) (- 1ℚ)
             (ℚ<-adding (2/3 - r) s (2/3 - r) s l l))

  upper : (s + s) - 1ℚ < 1/3 + radius k
  upper = transport ((s + s) - 1ℚ <_)
           (ap (_- 1ℚ)
             (double-upper 2/3 r ∙ ap ((2/3 + 2/3) +_) (radius-halves k))
            ∙ plus-minus-one-later (2/3 + 2/3) (radius k)
            ∙ ap (_+ radius k) 2/3+2/3-1)
           (ℚ<-addition-preserves-order (s + s) ((2/3 + r) + (2/3 + r)) (- 1ℚ)
             (ℚ<-adding s (2/3 + r) s (2/3 + r) m m))

cell-digits : (k : ℕ) (b : 𝟚) (s : ℚ) → cell k b s
            → (q : ℕ) → q <ℕ k → digits s q ＝ altfrom b q
cell-digits 0        b s c q        l = 𝟘-elim l
cell-digits (succ k) b s c 0        l = pr₁ (cell-reading k b s c)
cell-digits (succ k) b s c (succ q) l = cell-digits k (complement b) (T s)
                                         (pr₂ (cell-reading k b s c)) q l

cell-in-𝕁 : (k : ℕ) (b : 𝟚) (s : ℚ) → cell k b s → s ∈𝕁
cell-in-𝕁 k ₀ s (l , m) =
 ℚ<-coarser-than-≤ 0ℚ s
  (ℚ≤-<-trans 0ℚ (1/3 - radius k) s
    (transport (_≤ 1/3 - radius k) 1/3-1/3
      (ℚ≤-adding 1/3 1/3 (- 1/3) (- radius k) (ℚ≤-refl 1/3)
        (ℚ≤-swap (radius k) 1/3 (radius-at-most-third k))))
    l) ,
 ℚ<-≤-trans s (1/3 + radius k) 1ℚ m
  (ℚ≤-trans (1/3 + radius k) (1/3 + 1/3) 1ℚ
    (ℚ≤-adding 1/3 1/3 (radius k) 1/3 (ℚ≤-refl 1/3) (radius-at-most-third k))
    (transport (_≤ 1ℚ) (1/3+1/3'' ⁻¹) (ℚ<-coarser-than-≤ 2/3 1ℚ 2/3<1)))
cell-in-𝕁 k ₁ s (l , m) =
 ℚ<-coarser-than-≤ 0ℚ s
  (ℚ≤-<-trans 0ℚ (2/3 - radius k) s
    (ℚ≤-trans 0ℚ 1/3 (2/3 - radius k) (ℚ<-coarser-than-≤ 0ℚ 1/3 0<1/3')
      (transport (_≤ 2/3 - radius k) 2/3-1/3
        (ℚ≤-adding 2/3 2/3 (- 1/3) (- radius k) (ℚ≤-refl 2/3)
          (ℚ≤-swap (radius k) 1/3 (radius-at-most-third k)))))
    l) ,
 ℚ<-≤-trans s (2/3 + radius k) 1ℚ m
  (transport (2/3 + radius k ≤_) 2/3+1/3''
    (ℚ≤-adding 2/3 2/3 (radius k) 1/3 (ℚ≤-refl 2/3) (radius-at-most-third k)))

centre-is-in-its-cells : (k : ℕ) (b : 𝟚) → cell k b (centre-of b)
centre-is-in-its-cells k b =
 transport (centre-of b - radius k <_) (minus-plus (centre-of b) (radius k))
  (ℚ<-addition-preserves-order'' (centre-of b - radius k) (radius k)
    (radius-is-positive k)) ,
 ℚ<-addition-preserves-order'' (centre-of b) (radius k) (radius-is-positive k)

\end{code}

Codes of vectors in the cells agree with the centre on the first k
blocks, so they are within 2⁻ᵏ of 1/4.

\begin{code}

code-blocks-agree
 : (m K k : ℕ) (w : ℕ → ℚ) → k ≤ℕ K
 → ((i : ℕ) → i <ℕ m → cell k (alt i) (w i))
 → (q : ℕ) → q <ℕ k
 → blockOf m (λ i → dig K w q i) ＝ blockOf m (altfrom (alt q))
code-blocks-agree m K k w l c q l' =
 blockOf-ext m (λ i → dig K w q i) (altfrom (alt q)) γ
 where
  γ : (i : ℕ) → i <ℕ m → dig K w q i ＝ altfrom (alt q) i
  γ i l'' = dig-is-digits K w q i (≤-trans (succ q) k K l' l)
          ∙ cell-digits k (alt i) (w i) (c i l'') q l'
          ∙ alt-swap i q

code-is-near-the-centre
 : (n K k : ℕ) (w : ℕ → ℚ) → k ≤ℕ K
 → ((i : ℕ) → i <ℕ succ (dbl n) → cell k (alt i) (w i))
 → close (pow½ k) (code (succ (dbl n)) K w) 1/4
code-is-near-the-centre n K k w l c =
 orbits-are-close (dbl n) (code-point (succ (dbl n)) K w) (λ q → point (alt q))
  (λ q i → dig K w q i) (λ q → altfrom (alt q))
  (code-point-in-𝕀 (succ (dbl n)) K w) (λ q → point-in-𝕀 (alt q))
  (code-orbit (succ (dbl n)) K w) (centre-orbit n)
  k 0
  (λ q l' → transport (λ x → blockOf (succ (dbl n)) (λ i → dig K w x i)
                           ＝ blockOf (succ (dbl n)) (altfrom (alt x)))
             (zero-left-neutral q ⁻¹)
             (code-blocks-agree (succ (dbl n)) K k w l c q l'))

close-gives-interval : (e x c r₁ r₂ : ℚ) → close e x c → e < c - r₁ → e < r₂ - c
                     → (r₁ < x) × (x < r₂)
close-gives-interval e x c r₁ r₂ (m , m') o o' =
 transport₂ _<_ (minus-plus r₁ c) (minus-plus x c)
  (ℚ<-addition-preserves-order (r₁ - c) (x - c) c
    (transport₂ _<_ (ℚ-minus-dist' c r₁) (ℚ-minus-dist' c x)
      (ℚ<-swap (c - x) (c - r₁) (ℚ≤-<-trans (c - x) e (c - r₁) m' o)))) ,
 transport₂ _<_ (minus-plus x c) (minus-plus r₂ c)
  (ℚ<-addition-preserves-order (x - c) (r₂ - c) c
    (ℚ≤-<-trans (x - c) e (r₂ - c) m o'))

\end{code}

Coordinates. Points of ℝⁿ are functions on Fin n, and index j is the
coordinate of the curve that j stands for. A rational vector on Fin n
extends to all coordinates by given values; the box of level k is the
set of points whose coordinates lie within half the radius of level k
around half the centres, so that twice a point of the box lies in the
cells. These are used by gist.RealCohesion.DigitCurve; they are here
because they have no real numbers and this module has no parameters.

\begin{code}

index : {n : ℕ} → Fin n → ℕ
index {0}      j       = 𝟘-elim j
index {succ n} 𝟎       = 0
index {succ n} (suc j) = succ (index j)

index-bound : {n : ℕ} (j : Fin n) → index j <ℕ n
index-bound {0}      j       = 𝟘-elim j
index-bound {succ n} 𝟎       = ⋆
index-bound {succ n} (suc j) = index-bound j

extend : (n : ℕ) → (Fin n → ℚ) → (ℕ → ℚ) → ℕ → ℚ
extend 0        v e i        = e i
extend (succ n) v e 0        = v 𝟎
extend (succ n) v e (succ i) = extend n (λ j → v (suc j)) (λ i' → e (succ i')) i

extend-at : (n : ℕ) (v : Fin n → ℚ) (e : ℕ → ℚ) (j : Fin n)
          → extend n v e (index j) ＝ v j
extend-at 0        v e j       = 𝟘-elim j
extend-at (succ n) v e 𝟎       = refl
extend-at (succ n) v e (suc j) =
 extend-at n (λ j' → v (suc j')) (λ i' → e (succ i')) j

extend-property : (n : ℕ) (v : Fin n → ℚ) (e : ℕ → ℚ) (R : ℕ → ℚ → 𝓤₀ ̇ )
                → ((j : Fin n) → R (index j) (v j))
                → ((i : ℕ) → n ≤ℕ i → R i (e i))
                → (i : ℕ) → R i (extend n v e i)
extend-property 0        v e R hv he i        = he i ⋆
extend-property (succ n) v e R hv he 0        = hv 𝟎
extend-property (succ n) v e R hv he (succ i) =
 extend-property n (λ j → v (suc j)) (λ i' → e (succ i')) (λ i' → R (succ i'))
  (λ j → hv (suc j)) (λ i' l → he (succ i') l) i

box-centre : ℕ → ℚ
box-centre i = half (centre-of (alt i))

box-radius : ℕ → ℚ
box-radius k = half (radius k)

doubled-cell : (k : ℕ) (i : ℕ) (x : ℚ)
             → box-centre i - box-radius k < x → x < box-centre i + box-radius k
             → cell k (alt i) (x + x)
doubled-cell k i x l m =
 transport (_< x + x)
  (double-lower (box-centre i) (box-radius k)
   ∙ ap₂ (λ a r → a - r) (halves-add-up (centre-of (alt i)))
      (halves-add-up (radius k)))
  (ℚ<-adding (box-centre i - box-radius k) x (box-centre i - box-radius k) x l
    l) ,
 transport (x + x <_)
  (double-upper (box-centre i) (box-radius k)
   ∙ ap₂ _+_ (halves-add-up (centre-of (alt i))) (halves-add-up (radius k)))
  (ℚ<-adding x (box-centre i + box-radius k) x (box-centre i + box-radius k) m
    m)

\end{code}
